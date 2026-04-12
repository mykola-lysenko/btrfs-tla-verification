#!/usr/bin/env python3
"""
btrfs_fsync_log_tree_simulate.py
----------------------------------
Generates synthetic bpftrace-format JSON traces for the BtrfsFsyncLogTree.tla
model (CVE-2024-37354: duplicate key crash from racing fsync + prealloc write).

Scenarios:
  --scenario buggy   : fsync logs prealloc extents that overlap due to
                       concurrent size-extending write → NoLogTreeDuplicate violated
  --scenario fixed   : fsync holds inode lock during log-one-extent sequence
                       → CONFORMS

Usage:
    python3 btrfs_fsync_log_tree_simulate.py --scenario buggy | \\
        python3 ../checkers/btrfs_fsync_log_tree_checker.py
"""

import argparse
import json
import time


def emit(events: list[dict]) -> None:
    print("# Simulated btrfs_fsync_log_tree trace")
    for e in events:
        print(json.dumps(e))
    print("# End of simulated trace")


def make_event(ts: int, tid: int, action: str, **kwargs) -> dict:
    return {"ts": ts, "tid": tid, "comm": f"xfs_io/{tid}", "action": action, **kwargs}


def buggy_scenario() -> list[dict]:
    """
    CVE-2024-37354 race:
    - File has prealloc extents: [4096, 8192) and [8192, 12288)
    - Writer (tid=200) extends i_size from 4096 to 8192 (writes into prealloc)
    - Fsync (tid=100) reads extent map, then writer updates i_size
    - Fsync logs both [4096, 8192) and [8192, 12288) as prealloc
    - But [8192, 12288) was already logged from a previous fsync
    - → duplicate key: two entries covering [8192, 12288)
    """
    t = int(time.time_ns())
    return [
        # Fsync starts
        make_event(t + 0,    100, "FsyncFile_Enter",    datasync=0),
        make_event(t + 100,  100, "LogInode_Enter"),
        # Fsync logs first extent [4096, 8192) — prealloc
        make_event(t + 200,  100, "LogOneExtent",       file_offset=4096,  len=4096),
        make_event(t + 300,  100, "LogOneExtent_Done",  ret=0),
        # Concurrent writer extends i_size to 8192 (writes into prealloc)
        make_event(t + 350,  200, "Write_Enter"),
        make_event(t + 400,  200, "WriteDuringFsync"),
        # Fsync now logs [8192, 12288) — but this was already in log tree
        # from a previous fsync (simulated by logging it twice)
        make_event(t + 450,  100, "LogOneExtent",       file_offset=8192,  len=4096),
        make_event(t + 500,  100, "LogOneExtent_Done",  ret=0),
        # Fsync tries to log [8192, 12288) again due to the race
        make_event(t + 550,  100, "LogOneExtent",       file_offset=8192,  len=4096),
        # btrfs_drop_extents fails with duplicate key
        make_event(t + 600,  100, "DropExtents_Enter"),
        make_event(t + 700,  100, "DropExtents_Done",   ret=-17),  # -EEXIST
        make_event(t + 800,  100, "LogInode_Done",      ret=-17),
        make_event(t + 900,  100, "FsyncFile_Done",     ret=-17, dur_us=900),
    ]


def fixed_scenario() -> list[dict]:
    """
    Fixed: fsync holds inode lock during the entire log-one-extent sequence.
    The writer cannot interleave between extent map read and log tree update.
    Each extent is logged exactly once.
    """
    t = int(time.time_ns())
    return [
        # Fsync starts, acquires inode lock
        make_event(t + 0,    100, "FsyncFile_Enter",    datasync=0),
        make_event(t + 100,  100, "LogInode_Enter"),
        # Fsync logs [4096, 8192) — unique
        make_event(t + 200,  100, "LogOneExtent",       file_offset=4096,  len=4096),
        make_event(t + 300,  100, "LogOneExtent_Done",  ret=0),
        # Fsync logs [8192, 12288) — unique
        make_event(t + 400,  100, "LogOneExtent",       file_offset=8192,  len=4096),
        make_event(t + 500,  100, "LogOneExtent_Done",  ret=0),
        # btrfs_drop_extents succeeds (no duplicates)
        make_event(t + 600,  100, "DropExtents_Enter"),
        make_event(t + 700,  100, "DropExtents_Done",   ret=0),
        make_event(t + 800,  100, "LogInode_Done",      ret=0),
        make_event(t + 900,  100, "FsyncFile_Done",     ret=0, dur_us=900),
        # Writer runs after fsync releases the lock — no race
        make_event(t + 1000, 200, "Write_Enter"),
    ]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Simulate fsync log tree traces")
    parser.add_argument("--scenario", choices=["buggy", "fixed"], default="buggy",
                        help="Which scenario to simulate (default: buggy)")
    args = parser.parse_args()

    if args.scenario == "buggy":
        print("# === BUGGY SCENARIO: CVE-2024-37354 fsync+prealloc race ===",
              flush=True)
        emit(buggy_scenario())
    else:
        print("# === FIXED SCENARIO: inode lock prevents race ===", flush=True)
        emit(fixed_scenario())
