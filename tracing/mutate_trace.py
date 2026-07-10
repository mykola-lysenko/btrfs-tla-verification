#!/usr/bin/env python3
"""Generate guaranteed-illegal mutants of a qgroup trace (negative validation).

Trace replay (validate-trace.sh) proves the model ACCEPTS real kernel
behavior; by itself that is one-sided — a model that allows everything also
passes. This tool generates mutant traces that violate per-task program
order or the queue->worker causality, i.e. orderings the real kernel cannot
produce. A faithful model must REJECT every one of them; a mutant that
survives (is accepted) exposes the model as too permissive at that point.

Operators (all guaranteed-illegal by construction):
  swap_same_task  swap two consecutive events of one task (program order)
  drop_enter      drop an *_Enter whose task has a later event
  dup_done        duplicate a *_Done event (task pc is already past it)
  early_worker    move the k-th RescanWorker_Enter before the k-th
                  RescanZeroTracking_Enter (pigeonhole: more worker starts
                  than possible queue events in that prefix)

Deliberately NOT mutated: cross-task swaps of independent events — those
are usually legal alternative interleavings the model SHOULD accept.

Each mutant is truncated shortly after the point where divergence is
guaranteed, so the TLC runs stay small. Unmutated truncated prefixes are
emitted as controls (must be ACCEPTED — guards against truncation causing
false kills).

Usage:
  mutate_trace.py trace.jsonl -o OUTDIR [--per-op N] [--pad N]

Writes OUTDIR/<name>.jsonl and OUTDIR/manifest.tsv:
  name  operator  expect  must_diverge_by  n_events  detail
"""
import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from trace_to_tla import OBSERVABLE, WORKER_ACTIONS  # noqa: E402


def load(path):
    events = []
    for line in open(path, errors="replace"):
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            e = json.loads(line)
        except json.JSONDecodeError:
            continue
        if e.get("action") in OBSERVABLE:
            events.append(e)
    events.sort(key=lambda e: e.get("ts", 0))
    return events


def task_of(e):
    return "worker" if e["action"] in WORKER_ACTIONS else f"t{e['tid']}"


def spread(candidates, n):
    """n samples spread evenly across the candidate list."""
    if len(candidates) <= n:
        return list(candidates)
    step = len(candidates) / n
    return [candidates[int(i * step)] for i in range(n)]


def gen_swap_same_task(events, n):
    """Swap globally-adjacent-in-task-order event pairs of the same task."""
    by_task = {}
    for i, e in enumerate(events):
        by_task.setdefault(task_of(e), []).append(i)
    pairs = [(idxs[k], idxs[k + 1])
             for idxs in by_task.values() for k in range(len(idxs) - 1)]
    pairs.sort()
    for i, j in spread(pairs, n):
        mutated = list(events)
        mutated[i], mutated[j] = mutated[j], mutated[i]
        yield (mutated, i,
               f"swap {task_of(events[i])} events at {i}<->{j} "
               f"({events[i]['action']} <-> {events[j]['action']})")


def gen_drop_enter(events, n):
    """Drop an *_Enter whose task has a later event (which becomes orphan)."""
    last_pos = {}
    for i, e in enumerate(events):
        last_pos[task_of(e)] = i
    cands = [i for i, e in enumerate(events)
             if e["action"].endswith("_Enter") and last_pos[task_of(e)] > i]
    for i in spread(cands, n):
        t = task_of(events[i])
        nxt = next(j for j in range(i + 1, len(events)) if task_of(events[j]) == t)
        mutated = events[:i] + events[i + 1:]
        yield (mutated, nxt - 1,
               f"drop {t} {events[i]['action']} at {i} "
               f"(orphans {events[nxt]['action']} at {nxt})")


def gen_dup_done(events, n):
    """Duplicate a *_Done immediately after itself."""
    cands = [i for i, e in enumerate(events) if e["action"].endswith("_Done")]
    for i in spread(cands, n):
        mutated = events[:i + 1] + [dict(events[i])] + events[i + 1:]
        yield (mutated, i + 1,
               f"duplicate {task_of(events[i])} {events[i]['action']} at {i}")


def gen_early_worker(events, n):
    """Move the k-th RescanWorker_Enter before the k-th ZeroTracking_Enter.

    The k-th zero-tracking has at most k-1 completed queue events before it,
    so a prefix that ends there cannot explain a k-th worker start.
    """
    w_enters = [i for i, e in enumerate(events) if e["action"] == "RescanWorker_Enter"]
    zt_enters = [i for i, e in enumerate(events)
                 if e["action"] == "RescanZeroTracking_Enter"]
    cands = [(k, w, zt_enters[k]) for k, w in enumerate(w_enters)
             if k < len(zt_enters) and zt_enters[k] < w]
    for k, w, dest in spread(cands, n):
        ev = events[w]
        mutated = events[:dest] + [ev] + [e for e in events[dest:] if e is not ev]
        yield (mutated, w + 1,
               f"move RescanWorker_Enter #{k + 1} from {w} to before "
               f"RescanZeroTracking_Enter #{k + 1} at {dest}")


OPERATORS = [
    ("swap_same_task", gen_swap_same_task),
    ("drop_enter", gen_drop_enter),
    ("dup_done", gen_dup_done),
    ("early_worker", gen_early_worker),
]


def write_mutant(outdir, name, events):
    """Re-stamp ts with the sequence index so the intended order is frozen."""
    path = outdir / f"{name}.jsonl"
    with open(path, "w") as f:
        for i, e in enumerate(events):
            f.write(json.dumps({**e, "ts": i + 1}) + "\n")
    return path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("trace")
    ap.add_argument("-o", "--outdir", required=True)
    ap.add_argument("--per-op", type=int, default=6)
    ap.add_argument("--pad", type=int, default=10,
                    help="events kept after the guaranteed-divergence point")
    args = ap.parse_args()

    events = load(args.trace)
    if len(events) < 20:
        sys.exit(f"only {len(events)} observable events in {args.trace}")
    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    rows = []
    # Controls: unmutated prefixes, must be ACCEPTED.
    for label, frac in [("early", 0.25), ("late", 0.9)]:
        cut = int(len(events) * frac)
        write_mutant(outdir, f"control_{label}", events[:cut])
        rows.append((f"control_{label}", "control", "ACCEPT", "-", cut,
                     f"unmutated prefix of {cut} events"))

    for op_name, gen in OPERATORS:
        for k, (mutated, diverge_by, detail) in enumerate(gen(events, args.per_op)):
            cut = min(len(mutated), diverge_by + 1 + args.pad)
            name = f"{op_name}_{k}"
            write_mutant(outdir, name, mutated[:cut])
            rows.append((name, op_name, "REJECT", diverge_by + 1, cut, detail))

    with open(outdir / "manifest.tsv", "w") as f:
        f.write("name\toperator\texpect\tmust_diverge_by\tn_events\tdetail\n")
        for r in rows:
            f.write("\t".join(str(x) for x in r) + "\n")

    n_mut = sum(1 for r in rows if r[1] != "control")
    print(f"wrote {n_mut} mutants + 2 controls to {outdir} "
          f"(from {len(events)} observable events)")


if __name__ == "__main__":
    main()
