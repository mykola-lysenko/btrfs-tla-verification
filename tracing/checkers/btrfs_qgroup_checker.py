#!/usr/bin/env python3
"""
btrfs_qgroup_checker.py
------------------------
Checks the NoUAF invariant from BtrfsQgroup.tla (CVE-2025-39759).

Invariant:
    NoUAF == ~(qgroup_tree_freed /\ rescan_running)
    (The qgroup tree must not be freed while a rescan is iterating it.)

Usage:
    sudo bpftrace btrfs_qgroup.bt | python3 btrfs_qgroup_checker.py
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from checker_base import BtrfsChecker, TraceEvent


class QgroupChecker(BtrfsChecker):
    def __init__(self):
        super().__init__(
            name="BtrfsQgroup",
            invariant="NoUAF (qgroup_tree not freed while rescan active)",
        )
        self.rescan_active_tids: set[int] = set()
        self.quotas_enabled = False
        self.qgroup_tree_freed = False

    def process_event(self, event: TraceEvent) -> None:
        action = event.action
        tid    = event.tid

        if action == "QuotaEnable_Done" and event.raw.get("ret", -1) == 0:
            self.quotas_enabled = True
            self.qgroup_tree_freed = False

        elif action == "QuotaDisable_Enter":
            pass  # disabling starts

        elif action == "QuotaDisable_Done":
            self.quotas_enabled = False

        elif action == "QgroupRescan_Enter":
            if not self.quotas_enabled:
                self.violation(
                    event,
                    "Rescan started while quotas are disabled — "
                    "should check quotas_enabled before starting worker",
                )
            self.rescan_active_tids.add(tid)

        elif action == "QgroupRescan_Done":
            self.rescan_active_tids.discard(tid)

        elif action == "RescanZeroTracking_Enter":
            self.rescan_active_tids.add(tid)

        elif action == "RescanZeroTracking_Done":
            self.rescan_active_tids.discard(tid)

        elif action == "FreeQgroupConfig_Enter":
            if self.rescan_active_tids:
                self.violation(
                    event,
                    f"NoUAF violated: btrfs_free_qgroup_config called while "
                    f"{len(self.rescan_active_tids)} rescan thread(s) active "
                    f"(tids={self.rescan_active_tids}). "
                    f"Fix: hold qgroup_lock in btrfs_free_qgroup_config.",
                )
            self.qgroup_tree_freed = True

        elif action == "FreeQgroupConfig_Done":
            pass


if __name__ == "__main__":
    checker = QgroupChecker()
    checker.run(sys.stdin)
    sys.exit(checker.exit_code())
