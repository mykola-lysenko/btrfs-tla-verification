#!/usr/bin/env python3
"""
btrfs_extent_buffer_lock_simulate.py
--------------------------------------
Generates synthetic bpftrace-format JSON traces for the
BtrfsExtentBufferLock.tla model.

Produces two scenarios:
  --scenario buggy   : Thread 1 acquires level 1 then tries level 2 (bottom-up)
                       → checker should report NoDeadlock violation
  --scenario fixed   : Thread 1 acquires level 2 then level 1 (top-down)
                       → checker should report CONFORMS

Usage:
    python3 btrfs_extent_buffer_lock_simulate.py --scenario buggy | \\
        python3 ../checkers/btrfs_extent_buffer_lock_checker.py

    python3 btrfs_extent_buffer_lock_simulate.py --scenario fixed | \\
        python3 ../checkers/btrfs_extent_buffer_lock_checker.py
"""

import argparse
import json
import time


def emit(events: list[dict]) -> None:
    print("# Simulated btrfs_extent_buffer_lock trace")
    for e in events:
        print(json.dumps(e))
    print("# End of simulated trace")


def make_event(ts: int, tid: int, action: str, **kwargs) -> dict:
    return {"ts": ts, "tid": tid, "comm": f"kworker/{tid}", "action": action, **kwargs}


def buggy_scenario() -> list[dict]:
    """
    Thread 1 (tid=100): acquires level 1 (leaf), then tries level 2 (internal)
    Thread 2 (tid=200): acquires level 2 (internal), then tries level 1 (leaf)
    → Classic ABBA deadlock via lock inversion
    """
    t = int(time.time_ns())
    return [
        # Thread 1 acquires level 1 (leaf) — OK so far
        make_event(t + 0,    100, "AcquireWrite",      level=1, bytenr=0x10000),
        make_event(t + 100,  100, "AcquireWrite_Done"),
        # Thread 2 acquires level 2 (internal) — OK so far
        make_event(t + 200,  200, "AcquireWrite",      level=2, bytenr=0x20000),
        make_event(t + 300,  200, "AcquireWrite_Done"),
        # Thread 1 tries to acquire level 2 while holding level 1 — VIOLATION
        make_event(t + 400,  100, "AcquireWrite",      level=2, bytenr=0x20000),
        # Thread 2 tries to acquire level 1 while holding level 2 — deadlock
        make_event(t + 500,  200, "AcquireWrite",      level=1, bytenr=0x10000),
        # Neither can proceed — deadlock
    ]


def fixed_scenario() -> list[dict]:
    """
    Thread 1 (tid=100): acquires level 2 (internal), then level 1 (leaf) — correct
    Thread 2 (tid=200): acquires level 2 (internal), then level 1 (leaf) — correct
    → No violation, threads serialize on level 2
    """
    t = int(time.time_ns())
    return [
        # Thread 1 acquires level 2 first (top-down)
        make_event(t + 0,    100, "AcquireWrite",      level=2, bytenr=0x20000),
        make_event(t + 100,  100, "AcquireWrite_Done"),
        # Thread 1 acquires level 1 (correct: going down)
        make_event(t + 200,  100, "AcquireWrite",      level=1, bytenr=0x10000),
        make_event(t + 300,  100, "AcquireWrite_Done"),
        # Thread 1 releases level 1, then level 2
        make_event(t + 400,  100, "Release",           level=1, bytenr=0x10000),
        make_event(t + 500,  100, "Release",           level=2, bytenr=0x20000),
        # Thread 2 acquires level 2 (now free)
        make_event(t + 600,  200, "AcquireWrite",      level=2, bytenr=0x20000),
        make_event(t + 700,  200, "AcquireWrite_Done"),
        # Thread 2 acquires level 1 (correct: going down)
        make_event(t + 800,  200, "AcquireWrite",      level=1, bytenr=0x10000),
        make_event(t + 900,  200, "AcquireWrite_Done"),
        # Thread 2 releases
        make_event(t + 1000, 200, "Release",           level=1, bytenr=0x10000),
        make_event(t + 1100, 200, "Release",           level=2, bytenr=0x20000),
    ]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Simulate extent buffer lock traces")
    parser.add_argument("--scenario", choices=["buggy", "fixed"], default="buggy",
                        help="Which scenario to simulate (default: buggy)")
    args = parser.parse_args()

    if args.scenario == "buggy":
        print("# === BUGGY SCENARIO: lock inversion (bottom-up acquisition) ===",
              flush=True)
        emit(buggy_scenario())
    else:
        print("# === FIXED SCENARIO: top-down acquisition ===", flush=True)
        emit(fixed_scenario())
