#!/usr/bin/env python3
"""
btrfs_fsync_log_tree_checker.py
---------------------------------
Checks the NoLogTreeDuplicate invariant from BtrfsFsyncLogTree.tla
(CVE-2024-37354).

Invariant:
    NoLogTreeDuplicate ==
        \A e1, e2 \in log_tree_entries :
            e1 /= e2 => ~Overlaps(e1, e2)

    where Overlaps(e1, e2) means the file offset ranges of e1 and e2 overlap.

Usage:
    sudo bpftrace btrfs_fsync_log_tree.bt | python3 btrfs_fsync_log_tree_checker.py
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from checker_base import BtrfsChecker, TraceEvent


def overlaps(start1: int, len1: int, start2: int, len2: int) -> bool:
    end1 = start1 + len1
    end2 = start2 + len2
    return start1 < end2 and start2 < end1


class FsyncLogTreeChecker(BtrfsChecker):
    def __init__(self):
        super().__init__(
            name="BtrfsFsyncLogTree",
            invariant="NoLogTreeDuplicate (no overlapping extents in log tree)",
        )
        # log_extents: list of (file_offset, length) tuples logged in current fsync
        # Keyed by tid to handle concurrent fsyncs
        self.log_extents: dict[int, list] = {}
        self.fsync_active: set[int] = set()

    def process_event(self, event: TraceEvent) -> None:
        action = event.action
        tid    = event.tid

        if action == "FsyncFile_Enter":
            self.fsync_active.add(tid)
            self.log_extents[tid] = []

        elif action == "FsyncFile_Done":
            self.fsync_active.discard(tid)
            self.log_extents.pop(tid, None)

        elif action == "LogOneExtent":
            file_offset = event.raw.get("file_offset", 0)
            length      = event.raw.get("len", 0)
            existing    = self.log_extents.get(tid, [])

            # Check for overlap with all previously logged extents in this fsync
            for (prev_off, prev_len) in existing:
                if overlaps(file_offset, length, prev_off, prev_len):
                    self.violation(
                        event,
                        f"NoLogTreeDuplicate violated: new extent "
                        f"[{file_offset}, {file_offset + length}) overlaps "
                        f"existing log entry [{prev_off}, {prev_off + prev_len}) "
                        f"in tid={tid} fsync. "
                        f"This is the CVE-2024-37354 duplicate key pattern.",
                    )

            existing.append((file_offset, length))
            self.log_extents[tid] = existing

        elif action == "DropExtents_Done":
            ret = event.raw.get("ret", 0)
            if ret != 0:
                self.violation(
                    event,
                    f"btrfs_drop_extents returned {ret} — likely duplicate key "
                    f"BUG() in log tree (CVE-2024-37354)",
                )


if __name__ == "__main__":
    checker = FsyncLogTreeChecker()
    checker.run(sys.stdin)
    sys.exit(checker.exit_code())
