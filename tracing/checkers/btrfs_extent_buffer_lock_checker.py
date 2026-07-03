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
        # held[tid] = {bytenr: level} for locks currently held by that
        # thread. Keyed by bytenr so a Release always removes its entry even
        # when the tracer could not read the level (-1) for one of the two
        # events — level-keyed tracking left stale entries behind and
        # produced false "inversion" reports.
        self.held: dict[int, dict[int, int]] = {}
        # waiting_for[tid] = (bytenr, level) the thread is trying to acquire
        self.waiting_for: dict[int, tuple] = {}

    def process_event(self, event: TraceEvent) -> None:
        tid = event.tid
        action = event.action

        if action == "AcquireWrite":
            level = event.raw.get("level", -1)
            bytenr = event.raw.get("bytenr", -1)
            owner = event.raw.get("owner", 0)
            # The tracer reads level/owner from the on-disk header at lock
            # ENTRY, but a freshly allocated buffer is locked BEFORE its
            # header is written — the read races and returns garbage
            # (observed: "level 122"). BTRFS_MAX_LEVEL is 8, so anything
            # >= 8 is a racy read; recycled page content can also yield a
            # plausible-but-wrong small level, which we cannot detect here.
            if level >= 8:
                level = -1
            # Log-tree blocks (owner -6/-7) are exempt from ordering checks:
            # they are only locked by the per-root log-writer context under
            # log_mutex, so cross-thread ABBA cannot arise, and the kernel
            # legitimately locks them bottom-up while building the log.
            # (Observed: tree-log level-1 acquisitions while holding log
            # leaves during fsync.) The TLA+ model covers main-tree locking.
            if owner >= 2**64 - 7:
                level = -1
            held = self.held[tid] = self.held.get(tid, {})
            # Lock ordering is only defined within one btree: locks in
            # different trees (fs tree vs extent tree vs csum tree...) are
            # independent domains, so compare levels only for the same owner.
            known = [l for (l, o) in held.values() if l >= 0 and o == owner]

            # Level unknown (tracer could not read the btrfs_header, e.g.
            # multi-page extent buffer with no contiguous mapping): still
            # track the lock by bytenr, but skip ordering checks.
            if level >= 0:
                # Check: is the thread trying to acquire a level HIGHER than
                # any level it currently holds? Bottom-up = violation.
                if known and level > max(known):
                    self.violation(
                        event,
                        f"Lock inversion: tid={tid} holds levels {sorted(known)} "
                        f"but is acquiring level {level} (must go top-down, high→low)",
                    )

            # ABBA deadlock: another thread HOLDS the exact lock (bytenr)
            # we want, while WAITING for a lock we hold. (The TLA+ model
            # had one lock per level, so it compared levels; on a real
            # kernel lock identity is the extent buffer bytenr.)
            for other_tid, other_held in self.held.items():
                if other_tid == tid:
                    continue
                if bytenr in other_held:
                    other_waiting = self.waiting_for.get(other_tid)
                    if other_waiting is not None and other_waiting[0] in held:
                        self.violation(
                            event,
                            f"Deadlock detected: tid={tid} wants bytenr {bytenr} "
                            f"level {level} (held by tid={other_tid}), and "
                            f"tid={other_tid} waits for bytenr {other_waiting[0]} "
                            f"(held by tid={tid})",
                        )

            self.waiting_for[tid] = (bytenr, level, owner)

        elif action == "AcquireWrite_Done":
            pending = self.waiting_for.pop(tid, None)
            if pending is not None:
                bytenr, level, owner = pending
                self.held.setdefault(tid, {})[bytenr] = (level, owner)

        elif action == "Release":
            bytenr = event.raw.get("bytenr", -1)
            held = self.held.get(tid)
            if held is not None:
                held.pop(bytenr, None)
                if not held:
                    self.held.pop(tid, None)

        elif action == "AcquireRead":
            level = event.raw.get("level", -1)
            owner = event.raw.get("owner", 0)
            if level < 0 or level >= 8 or owner >= 2**64 - 7:
                return
            known = [l for (l, o) in self.held.get(tid, {}).values()
                     if l >= 0 and o == owner]
            if known and level > max(known):
                self.violation(
                    event,
                    f"Read lock inversion: tid={tid} holds levels {sorted(known)} "
                    f"but is acquiring read lock at level {level}",
                )

        elif action == "ReleaseRead":
            pass  # Read locks don't affect write-lock ordering check


if __name__ == "__main__":
    checker = ExtentBufferLockChecker()
    checker.run(sys.stdin)
    sys.exit(checker.exit_code())
