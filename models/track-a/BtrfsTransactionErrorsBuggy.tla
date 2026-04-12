----------------------- MODULE BtrfsTransactionErrorsBuggy -----------------------
EXTENDS Integers, Sequences, TLC

(*
 * BtrfsTransactionErrorsBuggy.tla
 *
 * Injects two bugs into the transaction commit error handling:
 *
 * BUG 1: Missing wake_up in abort path.
 * In the correct kernel, __btrfs_abort_transaction calls:
 *   wake_up(&fs_info->transaction_wait);
 *   wake_up(&fs_info->transaction_blocked_wait);
 * This ensures all blocked waiters are woken up.
 * If these wake_up calls are missing, waiters block forever (deadlock).
 *
 * BUG 2: Missing fs_error flag in abort path.
 * If btrfs_abort_transaction fails to set the fs_error flag, new
 * transactions can start after an abort, potentially writing to a
 * corrupted filesystem.
 *)

VARIABLES
    trans_state,
    fs_error,
    waiter_state

vars == <<trans_state, fs_error, waiter_state>>

Init ==
    /\ trans_state = "RUNNING"
    /\ fs_error = FALSE
    /\ waiter_state = "RUNNING"

CommitStart ==
    /\ trans_state = "RUNNING"
    /\ fs_error = FALSE
    /\ trans_state' = "COMMIT_START"
    /\ UNCHANGED <<fs_error, waiter_state>>

CommitDoing ==
    /\ trans_state = "COMMIT_START"
    /\ fs_error = FALSE
    /\ trans_state' = "COMMIT_DOING"
    /\ UNCHANGED <<fs_error, waiter_state>>

CommitUnblocked ==
    /\ trans_state = "COMMIT_DOING"
    /\ fs_error = FALSE
    /\ trans_state' = "UNBLOCKED"
    /\ UNCHANGED <<fs_error, waiter_state>>

CommitCompleted ==
    /\ trans_state = "UNBLOCKED"
    /\ fs_error = FALSE
    /\ trans_state' = "COMPLETED"
    /\ UNCHANGED <<fs_error, waiter_state>>

\* BUG 1: Error abort WITHOUT waking up waiters
Bug1ErrorInDoing ==
    /\ trans_state = "COMMIT_DOING"
    /\ fs_error = FALSE
    /\ trans_state' = "ABORTED"
    /\ fs_error' = TRUE
    \* BUG: No wake_up call! Waiters remain in "WAITING" state.
    /\ UNCHANGED <<waiter_state>>

\* BUG 2: Error abort WITHOUT setting fs_error
Bug2ErrorInDoing ==
    /\ trans_state = "COMMIT_DOING"
    /\ fs_error = FALSE
    /\ trans_state' = "ABORTED"
    \* BUG: fs_error is NOT set!
    /\ UNCHANGED <<fs_error, waiter_state>>

\* New transaction starts (should be blocked if fs_error = TRUE)
NewTransactionStart ==
    /\ trans_state = "ABORTED"
    /\ fs_error = FALSE  \* Only allowed if no error (Bug 2 makes this possible)
    /\ trans_state' = "RUNNING"
    /\ UNCHANGED <<fs_error, waiter_state>>

WaiterBlocks ==
    /\ waiter_state = "RUNNING"
    /\ trans_state \in {"COMMIT_START", "COMMIT_DOING"}
    /\ waiter_state' = "WAITING"
    /\ UNCHANGED <<trans_state, fs_error>>

WaiterWakes ==
    /\ waiter_state = "WAITING"
    /\ trans_state \in {"UNBLOCKED", "COMPLETED", "ABORTED"}
    /\ waiter_state' = "WOKEN"
    /\ UNCHANGED <<trans_state, fs_error>>

Next ==
    \/ CommitStart
    \/ CommitDoing
    \/ CommitUnblocked
    \/ CommitCompleted
    \/ Bug1ErrorInDoing
    \/ Bug2ErrorInDoing
    \/ NewTransactionStart
    \/ WaiterBlocks
    \/ WaiterWakes

Fairness ==
    /\ WF_vars(CommitStart)
    /\ WF_vars(CommitDoing)
    /\ WF_vars(CommitUnblocked)
    /\ WF_vars(CommitCompleted)
    /\ WF_vars(Bug1ErrorInDoing)
    /\ WF_vars(Bug2ErrorInDoing)
    /\ WF_vars(WaiterBlocks)
    /\ WF_vars(WaiterWakes)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* INVARIANTS AND PROPERTIES

\* Bug 1: Waiter must eventually be woken (liveness)
\* This will FAIL because Bug1ErrorInDoing doesn't wake the waiter
WaiterNeverStuck ==
    (waiter_state = "WAITING") ~> (waiter_state = "WOKEN")

\* Bug 2: After abort, no new transaction should start
\* This will FAIL because Bug2ErrorInDoing doesn't set fs_error
NoNewTransAfterAbort ==
    [](trans_state = "ABORTED" => ~<>(trans_state = "RUNNING"))

=============================================================================
