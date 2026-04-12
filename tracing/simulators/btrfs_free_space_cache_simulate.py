#!/usr/bin/env python3
"""
btrfs_free_space_cache_simulate.py
------------------------------------
Generates synthetic bpftrace-format JSON traces for the
BtrfsFreeSpaceCache.tla model (double-add race condition).

Scenarios:
  --scenario buggy   : Two threads both add the same bytenr to the cache
                       → NoDoubleAdd violated
  --scenario fixed   : Proper serialization prevents double-add
                       → CONFORMS

Usage:
    python3 btrfs_free_space_cache_simulate.py --scenario buggy | \\
        python3 ../checkers/btrfs_free_space_cache_checker.py
"""

import argparse
import json
import time


def emit(events: list[dict]) -> None:
    print("# Simulated btrfs_free_space_cache trace")
    for e in events:
        print(json.dumps(e))
    print("# End of simulated trace")


def make_event(ts: int, tid: int, action: str, **kwargs) -> dict:
    return {"ts": ts, "tid": tid, "comm": f"kworker/{tid}", "action": action, **kwargs}


def buggy_scenario() -> list[dict]:
    t = int(time.time_ns())
    BYTENR = 0x400000
    SIZE   = 0x10000
    return [
        # Block group caching starts — both threads see the same uncached extent
        make_event(t + 0,   100, "CacheBlockGroup_Start", load_only=0),
        make_event(t + 0,   200, "CacheBlockGroup_Start", load_only=0),
        # Both threads call btrfs_add_free_space for the same bytenr
        make_event(t + 100, 100, "AddFreeSpace", bytenr=BYTENR, size=SIZE),
        make_event(t + 100, 200, "AddFreeSpace", bytenr=BYTENR, size=SIZE),  # double-add
        make_event(t + 200, 100, "AddFreeSpace_Done", ret=0),
        make_event(t + 200, 200, "AddFreeSpace_Done", ret=0),
        make_event(t + 300, 100, "CacheBlockGroup_Done", ret=0),
        make_event(t + 300, 200, "CacheBlockGroup_Done", ret=0),
    ]


def fixed_scenario() -> list[dict]:
    t = int(time.time_ns())
    BYTENR = 0x400000
    SIZE   = 0x10000
    return [
        # Only one thread caches the block group (serialized)
        make_event(t + 0,   100, "CacheBlockGroup_Start", load_only=0),
        make_event(t + 100, 100, "AddFreeSpace", bytenr=BYTENR, size=SIZE),
        make_event(t + 200, 100, "AddFreeSpace_Done", ret=0),
        make_event(t + 300, 100, "CacheBlockGroup_Done", ret=0),
        # Second thread waits for cache to be done, then skips caching
        make_event(t + 400, 200, "WaitCacheDone_Enter"),
        make_event(t + 500, 200, "WaitCacheDone_Done", wait_us=100),
        # Second thread removes the extent (allocation)
        make_event(t + 600, 200, "RemoveFreeSpace", bytenr=BYTENR, size=SIZE),
    ]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Simulate free space cache traces")
    parser.add_argument("--scenario", choices=["buggy", "fixed"], default="buggy")
    args = parser.parse_args()

    if args.scenario == "buggy":
        print("# === BUGGY SCENARIO: double-add race ===", flush=True)
        emit(buggy_scenario())
    else:
        print("# === FIXED SCENARIO: serialized caching ===", flush=True)
        emit(fixed_scenario())
