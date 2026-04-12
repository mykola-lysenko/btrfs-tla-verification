#!/usr/bin/env python3
"""
btrfs_free_space_cache_checker.py
-----------------------------------
Checks the NoDoubleAdd invariant from BtrfsFreeSpaceCache.tla.

Invariant:
    NoDoubleAdd == \A b \in DOMAIN cache: cache[b] <= 1
    (No bytenr appears more than once in the free space cache.)

Usage:
    sudo bpftrace btrfs_free_space_cache.bt | python3 btrfs_free_space_cache_checker.py
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from checker_base import BtrfsChecker, TraceEvent


class FreeSpaceCacheChecker(BtrfsChecker):
    def __init__(self):
        super().__init__(
            name="BtrfsFreeSpaceCache",
            invariant="NoDoubleAdd",
        )
        # cache: bytenr -> count of times it appears in the cache
        self.cache: dict[int, int] = {}

    def process_event(self, event: TraceEvent) -> None:
        action = event.action

        if action == "AddFreeSpace":
            bytenr = event.raw.get("bytenr", -1)
            size   = event.raw.get("size", 0)
            count  = self.cache.get(bytenr, 0) + 1
            self.cache[bytenr] = count
            if count > 1:
                self.violation(
                    event,
                    f"NoDoubleAdd violated: bytenr={bytenr} size={size} "
                    f"added {count} times to free space cache",
                )

        elif action == "RemoveFreeSpace":
            bytenr = event.raw.get("bytenr", -1)
            count  = self.cache.get(bytenr, 0)
            if count > 0:
                self.cache[bytenr] = count - 1
            else:
                self.violation(
                    event,
                    f"RemoveFreeSpace on bytenr={bytenr} which is not in cache "
                    f"(possible double-remove or missed add)",
                )


if __name__ == "__main__":
    checker = FreeSpaceCacheChecker()
    checker.run(sys.stdin)
    sys.exit(checker.exit_code())
