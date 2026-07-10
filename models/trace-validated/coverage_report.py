#!/usr/bin/env python3
"""Transition-coverage report for a trace-validation run.

Answers: which actions of BtrfsQgroupLifecycle did the replayed trace
actually exercise?  "TRACE ACCEPTED" alone only says the model can explain
the trace; this report says how much of the model the trace vouches for.

Reads the TLC log of a validate-trace.sh run made with `-coverage 1`.
TLC attributes evaluation counts to line/col ranges of the spec; this script
maps each range back to the enclosing action definition.  An action counts
as FIRED only if its final UNCHANGED conjunct was evaluated (a count on the
guard line alone means the action was considered but never taken).

Usage:
  coverage_report.py <tlc.log> [--model BtrfsQgroupLifecycle.tla]
                               [--tracedata BtrfsQgroupTraceData.tla]

Exit code: 0 always (this is a report, not a gate).
"""
import argparse
import re
import sys
from collections import Counter
from pathlib import Path

MODULE = "BtrfsQgroupLifecycle"

# Operators in the model that are not actions of the next-state relation.
NON_ACTIONS = {"Worker", "Tasks", "NoTask", "vars", "UserPCs", "WorkerPCs",
               "TypeOK", "Init", "Observable", "Internal", "ObservableNames",
               "Next", "Spec", "NoUAF"}

DEF_RE = re.compile(r"^([A-Za-z][A-Za-z0-9_]*)\s*(?:\([^)]*\))?\s*==")
# Top-level coverage entries (sub-expression lines are prefixed with '|').
ENTRY_RE = re.compile(
    r"^\s*(?:<(?P<name>\w+) )?line (?P<line>\d+), col \d+ to line \d+, col \d+"
    r" of module (?P<module>\w+)(?: \([\d ]+\))?>?: (?P<count>\d+)(?::\d+)?\s*$")


def scan_defs(model_path):
    """[(name, start_line, end_line, fire_line)] for every action operator.

    fire_line = line of the last UNCHANGED in the body: evaluated iff the
    action was actually taken (every action's final conjunct is UNCHANGED).
    """
    lines = Path(model_path).read_text().splitlines()
    starts = [(i + 1, m.group(1)) for i, ln in enumerate(lines)
              if (m := DEF_RE.match(ln))]
    defs = []
    for (start, name), (nxt, _) in zip(starts, starts[1:] + [(len(lines) + 1, "")]):
        if name in NON_ACTIONS:
            continue
        body = range(start, nxt)
        unchanged = [n for n in body if n <= len(lines) and "UNCHANGED" in lines[n - 1]]
        if not unchanged:
            continue   # not an action (no frame conjunct)
        defs.append((name, start, nxt - 1, unchanged[-1]))
    return defs


def parse_coverage(log_path):
    """{line -> count} from the LAST coverage block, MODULE entries only."""
    text = Path(log_path).read_text(errors="replace")
    blocks = text.split("The coverage statistics")
    if len(blocks) < 2:
        sys.exit(f"no coverage block in {log_path} (was TLC run with -coverage 1?)")
    counts = {}
    for ln in blocks[-1].splitlines():
        if ln.lstrip().startswith("|"):
            continue
        m = ENTRY_RE.match(ln)
        if m and m.group("module") == MODULE:
            line, n = int(m.group("line")), int(m.group("count"))
            counts[line] = max(counts.get(line, 0), n)
    return counts


def trace_action_counts(tracedata_path):
    if not tracedata_path or not Path(tracedata_path).exists():
        return None
    return Counter(re.findall(r'action \|-> "(\w+)"', Path(tracedata_path).read_text()))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    here = Path(__file__).resolve().parent
    ap.add_argument("--model", default=str(here / "BtrfsQgroupLifecycle.tla"))
    ap.add_argument("--tracedata", default=str(here / "BtrfsQgroupTraceData.tla"))
    args = ap.parse_args()

    defs = scan_defs(args.model)
    cov = parse_coverage(args.log)

    fired = {}
    for name, start, end, fire_line in defs:
        fired[name] = cov.get(fire_line, 0)

    order = [name for name, *_ in defs]
    exercised = [n for n in order if fired[n] > 0]
    missed = [n for n in order if fired[n] == 0]

    print("== Transition coverage (evaluation counts; 0 = never taken) ==")
    width = max(len(n) for n in order)
    for name in order:
        mark = "" if fired[name] else "   << NEVER EXERCISED"
        print(f"  {name:<{width}}  {fired[name]:>6}{mark}")
    print(f"\n== {len(exercised)}/{len(order)} model actions exercised by this trace ==")
    if missed:
        print("  never exercised: " + ", ".join(missed))

    # Branch splits derivable from action-flow arithmetic (an action's count
    # minus its sole successor's count = times the other branch was taken).
    def d(a, b):
        return fired.get(a, 0) - fired.get(b, 0)
    print("\n== Derived branch coverage ==")
    print(f"  E_Check early-exit (quota already on) : {d('E_Check', 'E_Create')}")
    print(f"  E_RescanInit -EINPROGRESS             : {d('E_RescanInit', 'E_ZTEnter')}")
    print(f"  R_Init early-exit (-EINPROGRESS etc.) : {d('R_Init', 'R_Commit')}")
    print(f"  D_Check early-exit (quota already off): {d('D_Check', 'D_ClearEnabled')}")
    print(f"  D_WaitRead saw rescanRunning = TRUE   : {fired.get('D_WaitBlocked', 0)}")
    print(f"  D_WaitRead saw rescanRunning = FALSE  : {d('D_WaitRead', 'D_WaitBlocked')}"
          f"   <- CVE hole precondition")

    trace = trace_action_counts(args.tracedata)
    if trace:
        print("\n== Observable events in trace ==")
        for a, n in sorted(trace.items()):
            print(f"  {a:<28} {n:>6}")


if __name__ == "__main__":
    main()
