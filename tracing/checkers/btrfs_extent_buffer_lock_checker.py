#!/usr/bin/env python3
"""
btrfs_extent_buffer_lock_checker.py
-------------------------------------
Checks the NoDeadlock invariant from BtrfsExtentBufferLock.tla against
a live bpftrace trace stream.

Invariant (from TLA+ model):
    NoDeadlock == ~DEADLOCK
    where DEADLOCK is TRUE when two threads each hold a lock at level L
    and are both waiting for a lock at level L' < L (bottom-up acquisition).

The kernel enforces top-down ordering: a thread must always acquire a lock
at a HIGHER level before a LOWER level (root=3 > internal=2 > leaf=1).
Acquiring a lower level while holding a higher level is correct.
Acquiring a higher level while holding a lower level is a violation.

Usage:
    sudo bpftrace btrfs_extent_buffer_lock.bt | python3 btrfs_extent_buffer_lock_checker.py
    # or replay a saved trace:
    python3 btrfs_extent_buffer_lock_checker.py < trace.jsonl
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from checker_base import BtrfsChecker, TraceEvent


class ExtentBufferLockChecker(BtrfsChecker):
    def __init__(self):
        super().__init__(
            name="BtrfsExtentBufferLock",
            invariant="NoDeadlock (top-down lock ordering)",
        )
        # held_levels[tid] = set of levels currently held by that thread
        self.held_levels: dict[int, set] = {}
        # waiting_for[tid] = level the thread is trying to acquire
        self.waiting_for: dict[int, int] = {}

    def process_event(self, event: TraceEvent) -> None:
        tid = event.tid
        action = event.action

        if action == "AcquireWrite":
            level = event.raw.get("level", -1)
            held = self.held_levels.get(tid, set())

            # Check: is the thread trying to acquire a level HIGHER than
            # any level it currently holds? That would be bottom-up = violation.
            if held and level > max(held):
                self.violation(
                    event,
                    f"Lock inversion: tid={tid} holds levels {sorted(held)} "
                    f"but is acquiring level {level} (must go top-down, high→low)",
                )

            # Check for potential deadlock: another thread holds this level
            for other_tid, other_held in self.held_levels.items():
                if other_tid == tid:
                    continue
                if level in other_held:
                    # Other thread holds the level we want
                    other_waiting = self.waiting_for.get(other_tid)
                    if other_waiting is not None and other_waiting in held:
                        self.violation(
                            event,
                            f"Deadlock detected: tid={tid} wants level {level} "
                            f"(held by tid={other_tid}), and tid={other_tid} "
                            f"wants level {other_waiting} (held by tid={tid})",
                        )

            self.waiting_for[tid] = level

        elif action == "AcquireWrite_Done":
            level = self.waiting_for.pop(tid, None)
            if level is not None:
                self.held_levels.setdefault(tid, set()).add(level)

        elif action == "Release":
            level = event.raw.get("level", -1)
            self.held_levels.get(tid, set()).discard(level)
            if not self.held_levels.get(tid):
                self.held_levels.pop(tid, None)

        elif action == "AcquireRead":
            level = event.raw.get("level", -1)
            held = self.held_levels.get(tid, set())
            if held and level > max(held):
                self.violation(
                    event,
                    f"Read lock inversion: tid={tid} holds levels {sorted(held)} "
                    f"but is acquiring read lock at level {level}",
                )

        elif action == "ReleaseRead":
            pass  # Read locks don't affect write-lock ordering check


if __name__ == "__main__":
    checker = ExtentBufferLockChecker()
    checker.run(sys.stdin)
    sys.exit(checker.exit_code())
