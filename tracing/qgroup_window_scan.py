#!/usr/bin/env python3
"""Direct wall-clock witness for the CVE-2025-39759 window in a raw trace.

The model replay (validate-trace.sh) proves the window is *reachable in the
abstraction*; on a massively concurrent hammer trace its hand partial-order
reduction can't reconstruct thousands of overlapping ops. This scans the
raw kprobe trace instead and reports concrete wall-clock overlaps — the same
windows the model's witness probes describe, but as timestamped empirical
events, no replay needed.

Each qgroup op is an [Enter_ts, Done_ts] interval per tid (matched as a
stack, so nested/reentrant calls pair correctly). Two ops "overlap" when
their intervals intersect. We report, per filesystem:

  free_vs_iter    FreeQgroupConfig overlaps a RescanZeroTracking on another
                  task — free walking the tree while it is being iterated
                  (the UAF itself; pre-fix it is unlocked).
  free_vs_worker  FreeQgroupConfig overlaps a RescanWorker (the worker is a
                  second victim; see the worker-race model finding).
  wait_vs_commit  a QuotaDisable's wait region overlaps another task's rescan
                  commit window [QgroupRescan_Enter .. RescanZeroTracking_
                  Enter] — FLAG_RESCAN set, rescan_running not yet: the exact
                  precondition of the early wait_for_completion return.

A hit does NOT mean the kernel faulted (a fixed kernel serialises via
qgroup_lock); it means the workload drove execution INTO the window the
model flags — which is the thing every prior trace failed to do.

Usage: qgroup_window_scan.py trace.jsonl [--fs FS] [--max N]
"""
import argparse
import json
import sys
from collections import defaultdict

PAIRS = {  # Enter action -> Done action
    "QuotaEnable_Enter": "QuotaEnable_Done",
    "QuotaDisable_Enter": "QuotaDisable_Done",
    "QgroupRescan_Enter": "QgroupRescan_Done",
    "RescanZeroTracking_Enter": "RescanZeroTracking_Done",
    "WaitRescanCompletion_Enter": "WaitRescanCompletion_Done",
    "FreeQgroupConfig_Enter": "FreeQgroupConfig_Done",
    "RescanWorker_Enter": "RescanWorker_Done",
}
DONE = set(PAIRS.values())


def load(path):
    evs = []
    for line in open(path, errors="replace"):
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            e = json.loads(line)
        except json.JSONDecodeError:
            continue
        if e.get("action") in PAIRS or e.get("action") in DONE:
            evs.append(e)
    evs.sort(key=lambda e: e.get("ts", 0))
    return evs


def intervals(evs):
    """Pair Enter/Done per (tid, kind) as a stack -> list of interval dicts.

    kind is the Enter action name. Each interval: {kind, tid, comm, fs, a, b}.
    """
    stacks = defaultdict(list)
    out = []
    done_to_enter = {v: k for k, v in PAIRS.items()}
    for e in evs:
        act = e["action"]
        if act in PAIRS:
            stacks[(e["tid"], act)].append(e)
        elif act in DONE:
            enter_act = done_to_enter[act]
            st = stacks[(e["tid"], enter_act)]
            if not st:
                continue
            s = st.pop()
            out.append({"kind": enter_act, "tid": e["tid"],
                        "comm": e.get("comm"), "fs": str(e.get("fs", "?")),
                        "a": s.get("ts", 0), "b": e.get("ts", 0)})
    return out


def overlaps(a0, a1, b0, b1):
    return a0 < b1 and b0 < a1


def commit_windows(evs):
    """[QgroupRescan_Enter .. next RescanZeroTracking_Enter same tid] per tid:
    the window where FLAG_RESCAN is set but rescan_running is not yet."""
    wins = []
    pending = {}
    for e in evs:
        if e["action"] == "QgroupRescan_Enter":
            pending[e["tid"]] = e
        elif e["action"] == "RescanZeroTracking_Enter" and e["tid"] in pending:
            s = pending.pop(e["tid"])
            wins.append({"tid": e["tid"], "fs": str(e.get("fs", "?")),
                         "a": s.get("ts", 0), "b": e.get("ts", 0)})
    return wins


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("trace")
    ap.add_argument("--fs", default=None, help="restrict to this fs_info value")
    ap.add_argument("--merge-fs", action="store_true",
                    help="treat all events as one filesystem (single-mount "
                         "workloads: heavy load drops some fs tags to 0, so "
                         "per-fs splitting undercounts overlaps)")
    ap.add_argument("--max", type=int, default=8, help="example hits to print per category")
    args = ap.parse_args()

    evs = load(args.trace)
    if args.fs:
        evs = [e for e in evs if str(e.get("fs", "?")) == args.fs]
    if args.merge_fs:
        for e in evs:
            e["fs"] = "merged"
    iv = intervals(evs)
    cw = commit_windows(evs)

    by_kind = defaultdict(list)
    for x in iv:
        by_kind[x["kind"]].append(x)
    frees = by_kind["FreeQgroupConfig_Enter"]
    zts = by_kind["RescanZeroTracking_Enter"]
    workers = by_kind["RescanWorker_Enter"]
    waits = by_kind["WaitRescanCompletion_Enter"]

    def scan(As, Bs, cross_task=True):
        hits = []
        Bs_sorted = sorted(Bs, key=lambda x: x["a"])
        for a in As:
            for b in Bs_sorted:
                if b["a"] >= a["b"]:
                    break
                if cross_task and b["tid"] == a["tid"]:
                    continue
                if a.get("fs") != b.get("fs"):
                    continue
                if overlaps(a["a"], a["b"], b["a"], b["b"]):
                    hits.append((a, b))
        return hits

    cats = [
        ("free_vs_iter", scan(frees, zts)),
        ("free_vs_worker", scan(frees, workers)),
        ("wait_vs_commit", scan(waits, cw)),
    ]

    print(f"scanned {len(evs)} events, {len(iv)} completed intervals"
          + (f" (fs {args.fs})" if args.fs else ""))
    print(f"  frees={len(frees)} zero_tracking={len(zts)} "
          f"workers={len(workers)} waits={len(waits)} commit_windows={len(cw)}")
    any_hit = False
    for name, hits in cats:
        n = len(hits)
        any_hit = any_hit or n > 0
        print(f"\n== {name}: {n} wall-clock overlap(s) ==")
        for a, b in hits[: args.max]:
            dur = (min(a["b"], b["b"]) - max(a["a"], b["a"])) / 1000.0
            bkind = b["kind"].split("_")[0] if "kind" in b else "RescanCommit"
            print(f"   t{a['tid']}({a['comm']}) {a['kind'].split('_')[0]} "
                  f"overlaps t{b['tid']} {bkind} "
                  f"for {dur:.1f}us  @ts={max(a['a'], b['a'])}")
    print()
    if any_hit:
        print("RESULT: WINDOW ENTERED — the workload drove execution into the "
              "CVE-2025-39759 interleaving (wall-clock witnessed).")
        sys.exit(0)
    else:
        print("RESULT: window never entered in this trace.")
        sys.exit(1)


if __name__ == "__main__":
    main()
