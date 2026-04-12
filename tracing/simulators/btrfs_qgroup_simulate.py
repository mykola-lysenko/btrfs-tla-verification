#!/usr/bin/env python3
"""
btrfs_qgroup_simulate.py
--------------------------
Generates synthetic bpftrace-format JSON traces for the BtrfsQgroup.tla
model (CVE-2025-39759: UAF between quota disable and qgroup rescan).

Scenarios:
  --scenario buggy   : Task B frees qgroup config while Task A is rescanning
                       → checker should report NoUAF violation
  --scenario fixed   : Task B waits for rescan to complete before freeing
                       → checker should report CONFORMS

Usage:
    python3 btrfs_qgroup_simulate.py --scenario buggy | \\
        python3 ../checkers/btrfs_qgroup_checker.py
"""

import argparse
import json
import time


def emit(events: list[dict]) -> None:
    print("# Simulated btrfs_qgroup trace")
    for e in events:
        print(json.dumps(e))
    print("# End of simulated trace")


def make_event(ts: int, tid: int, action: str, **kwargs) -> dict:
    return {"ts": ts, "tid": tid, "comm": f"kworker/{tid}", "action": action, **kwargs}


def buggy_scenario() -> list[dict]:
    """
    CVE-2025-39759 race:
    Task A (tid=100): enters btrfs_qgroup_rescan -> qgroup_rescan_zero_tracking
    Task B (tid=200): enters btrfs_quota_disable -> btrfs_free_qgroup_config
                      WITHOUT waiting for Task A to finish
    """
    t = int(time.time_ns())
    return [
        # Setup: quotas are enabled
        make_event(t + 0,    0,   "QuotaEnable_Done",          ret=0),
        # Task A starts rescan
        make_event(t + 100,  100, "QgroupRescan_Enter"),
        make_event(t + 200,  100, "RescanZeroTracking_Enter"),
        # Task B starts quota disable — does NOT wait for rescan
        make_event(t + 300,  200, "QuotaDisable_Enter"),
        # Task B calls btrfs_qgroup_wait_for_completion — but rescan_running
        # is still false at this point (CVE bug: check is too early)
        make_event(t + 400,  200, "WaitRescanCompletion_Enter"),
        make_event(t + 500,  200, "WaitRescanCompletion_Done",  ret=0),
        # Task B frees qgroup config while Task A is still iterating — UAF!
        make_event(t + 600,  200, "FreeQgroupConfig_Enter"),
        make_event(t + 700,  200, "FreeQgroupConfig_Done"),
        make_event(t + 800,  200, "QuotaDisable_Done"),
        # Task A continues iterating freed memory
        make_event(t + 900,  100, "RescanZeroTracking_Done",    ret=0),
        make_event(t + 1000, 100, "QgroupRescan_Done",          ret=0),
    ]


def fixed_scenario() -> list[dict]:
    """
    Fixed: Task B holds qgroup_lock in btrfs_free_qgroup_config,
    and Task A checks quotas_enabled before starting rescan worker.
    The race window is closed.
    """
    t = int(time.time_ns())
    return [
        # Setup: quotas are enabled
        make_event(t + 0,    0,   "QuotaEnable_Done",          ret=0),
        # Task A starts rescan — sets rescan_running = true BEFORE Task B checks
        make_event(t + 100,  100, "QgroupRescan_Enter"),
        make_event(t + 200,  100, "RescanZeroTracking_Enter"),
        # Task B starts quota disable — waits for rescan to complete (fixed)
        make_event(t + 300,  200, "QuotaDisable_Enter"),
        make_event(t + 400,  200, "WaitRescanCompletion_Enter"),
        # Task A finishes rescan
        make_event(t + 500,  100, "RescanZeroTracking_Done",    ret=0),
        make_event(t + 600,  100, "QgroupRescan_Done",          ret=0),
        # Task B's wait returns — rescan is now done
        make_event(t + 700,  200, "WaitRescanCompletion_Done",  ret=0),
        # Task B safely frees qgroup config
        make_event(t + 800,  200, "FreeQgroupConfig_Enter"),
        make_event(t + 900,  200, "FreeQgroupConfig_Done"),
        make_event(t + 1000, 200, "QuotaDisable_Done"),
    ]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Simulate qgroup UAF traces")
    parser.add_argument("--scenario", choices=["buggy", "fixed"], default="buggy",
                        help="Which scenario to simulate (default: buggy)")
    args = parser.parse_args()

    if args.scenario == "buggy":
        print("# === BUGGY SCENARIO: CVE-2025-39759 qgroup rescan UAF ===",
              flush=True)
        emit(buggy_scenario())
    else:
        print("# === FIXED SCENARIO: rescan completes before free ===", flush=True)
        emit(fixed_scenario())
