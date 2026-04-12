#!/usr/bin/env python3
"""
btrfs_transaction_chain_checker.py
------------------------------------
Checks the NoDeadlock invariant from BtrfsTransactionChain.tla.

Invariant:
    NoDeadlock == ~(\E t1, t2 \in Threads :
        t1 /= t2
        /\ thread_state[t1] = "WaitingForTx"
        /\ thread_state[t2] = "WaitingForTx"
        /\ tx_held_by[t1] = t2
        /\ tx_held_by[t2] = t1)

Simplified check: detect threads that have been blocked in
wait_current_trans for longer than a configurable timeout (default 30s),
which is a strong signal of a deadlock in practice.

Also detects the specific CVE-2025-71194 pattern:
    TRANS_JOIN waits unconditionally for TRANS_STATE_COMMIT_START.

Usage:
    sudo bpftrace btrfs_transaction_chain.bt | python3 btrfs_transaction_chain_checker.py
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from checker_base import BtrfsChecker, TraceEvent

# Deadlock threshold: if a thread waits more than this many microseconds
# in wait_current_trans, flag it as a potential deadlock.
DEADLOCK_THRESHOLD_US = 30_000_000  # 30 seconds


class TransactionChainChecker(BtrfsChecker):
    def __init__(self):
        super().__init__(
            name="BtrfsTransactionChain",
            invariant="NoDeadlock (no circular wait between transactions)",
        )
        # wait_enter_ts[tid] = timestamp (ns) when thread entered wait_current_trans
        self.wait_enter_ts: dict[int, int] = {}
        # active_transactions: set of tids that have started but not committed
        self.active_tx_tids: set[int] = set()
        # waiting_tids: set of tids currently blocked in wait_current_trans
        self.waiting_tids: set[int] = set()

    def process_event(self, event: TraceEvent) -> None:
        action = event.action
        tid    = event.tid

        if action == "StartTransaction_Done":
            self.active_tx_tids.add(tid)

        elif action in ("CommitTransaction_Done", "EndTransaction"):
            self.active_tx_tids.discard(tid)

        elif action == "WaitCurrentTrans_Enter":
            self.wait_enter_ts[tid] = event.ts
            self.waiting_tids.add(tid)

            # CVE-2025-71194 pattern: if ALL active transaction holders are
            # also waiting, we have a circular wait
            if self.active_tx_tids and self.active_tx_tids.issubset(self.waiting_tids):
                self.violation(
                    event,
                    f"NoDeadlock violated: all active transaction threads "
                    f"({self.active_tx_tids}) are now waiting in wait_current_trans. "
                    f"Circular wait detected (CVE-2025-71194 pattern).",
                )

        elif action == "WaitCurrentTrans_Done":
            enter_ts = self.wait_enter_ts.pop(tid, None)
            self.waiting_tids.discard(tid)
            wait_us  = event.raw.get("wait_us", 0)
            if wait_us > DEADLOCK_THRESHOLD_US:
                self.violation(
                    event,
                    f"Potential deadlock: tid={tid} waited {wait_us / 1_000_000:.1f}s "
                    f"in wait_current_trans (threshold={DEADLOCK_THRESHOLD_US // 1_000_000}s)",
                )

        elif action == "AbortTransaction":
            errno = event.raw.get("errno", 0)
            self.active_tx_tids.discard(tid)
            self.waiting_tids.discard(tid)
            self.wait_enter_ts.pop(tid, None)


if __name__ == "__main__":
    checker = TransactionChainChecker()
    checker.run(sys.stdin)
    sys.exit(checker.exit_code())
