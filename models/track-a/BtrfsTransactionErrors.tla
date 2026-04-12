----------------------- MODULE BtrfsTransactionErrors -----------------------
EXTENDS Integers, Sequences, TLC

(*
 * BtrfsTransactionErrors.tla
 *
 * Models the error handling paths in btrfs_commit_transaction.
 * A transaction commit goes through multiple states:
 * UNBLOCKED -> COMMIT_START -> COMMIT_DOING -> UNBLOCKED -> SUPER_COMMITTED -> COMPLETED
 *
 * At almost any point, an allocation (-ENOMEM) or IO (-EIO) error can occur.
 * When this happens, the code jumps to `cleanup_transaction()`, which:
 * 1. Calls btrfs_abort_transaction (sets fs_info->fs_error, trans->aborted)
 * 2. Wakes up all waiters
 * 3. Removes the transaction from the running list
 * 4. Cleans up the transaction state
 *
 * We model:
 * - The commit state machine.
 * - Waiters (e.g., extwriters, normal writers) that block on the state.
 * - Injected failures at various stages.
 * - The cleanup path.
 *
 * The key property: if a commit fails and aborts, ALL waiters must be woken
 * up (none left blocked forever), and the filesystem must be marked as
 * ERROR, preventing new transactions from starting.
 *)

VARIABLES
    trans_state,      \* "RUNNING", "COMMIT_START", "COMMIT_DOING", "UNBLOCKED", "SUPER_COMMITTED", "COMPLETED", "ABORTED"
    fs_error,         \* TRUE if the filesystem is aborted
    waiter_state      \* "RUNNING", "WAITING", "WOKEN"

vars == <<trans_state, fs_error, waiter_state>>

Init ==
    /\ trans_state = "RUNNING"
    /\ fs_error = FALSE
    /\ waiter_state = "RUNNING"

-----------------------------------------------------------------------------
\* NORMAL COMMIT PATH

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

CommitSuper ==
    /\ trans_state = "UNBLOCKED"
    /\ fs_error = FALSE
    /\ trans_state' = "SUPER_COMMITTED"
    /\ UNCHANGED <<fs_error, waiter_state>>

CommitCompleted ==
    /\ trans_state = "SUPER_COMMITTED"
    /\ fs_error = FALSE
    /\ trans_state' = "COMPLETED"
    /\ UNCHANGED <<fs_error, waiter_state>>

-----------------------------------------------------------------------------
\* ERROR INJECTION PATHS

\* Error during COMMIT_START (e.g., waiting for writers)
ErrorInStart ==
    /\ trans_state = "COMMIT_START"
    /\ fs_error = FALSE
    /\ trans_state' = "ABORTED"
    /\ fs_error' = TRUE
    /\ waiter_state' = (IF waiter_state = "WAITING" THEN "WOKEN" ELSE waiter_state)

\* Error during COMMIT_DOING (e.g., btrfs_run_delayed_refs fails)
ErrorInDoing ==
    /\ trans_state = "COMMIT_DOING"
    /\ fs_error = FALSE
    /\ trans_state' = "ABORTED"
    /\ fs_error' = TRUE
    /\ waiter_state' = (IF waiter_state = "WAITING" THEN "WOKEN" ELSE waiter_state)

\* Error writing the superblock
ErrorInSuper ==
    /\ trans_state = "UNBLOCKED"
    /\ fs_error = FALSE
    /\ trans_state' = "ABORTED"
    /\ fs_error' = TRUE
    /\ waiter_state' = (IF waiter_state = "WAITING" THEN "WOKEN" ELSE waiter_state)

-----------------------------------------------------------------------------
\* WAITER PATH

\* A writer decides to wait for the transaction to unblock
WaiterBlocks ==
    /\ waiter_state = "RUNNING"
    /\ trans_state \in {"COMMIT_START", "COMMIT_DOING"}
    /\ waiter_state' = "WAITING"
    /\ UNCHANGED <<trans_state, fs_error>>

\* Waiter wakes up when the transaction reaches UNBLOCKED or is ABORTED
WaiterWakes ==
    /\ waiter_state = "WAITING"
    /\ trans_state \in {"UNBLOCKED", "SUPER_COMMITTED", "COMPLETED", "ABORTED"}
    /\ waiter_state' = "WOKEN"
    /\ UNCHANGED <<trans_state, fs_error>>

-----------------------------------------------------------------------------

Next ==
    \/ CommitStart
    \/ CommitDoing
    \/ CommitUnblocked
    \/ CommitSuper
    \/ CommitCompleted
    \/ ErrorInStart
    \/ ErrorInDoing
    \/ ErrorInSuper
    \/ WaiterBlocks
    \/ WaiterWakes

Fairness ==
    /\ WF_vars(CommitStart)
    /\ WF_vars(CommitDoing)
    /\ WF_vars(CommitUnblocked)
    /\ WF_vars(CommitSuper)
    /\ WF_vars(CommitCompleted)
    /\ WF_vars(ErrorInStart)
    /\ WF_vars(ErrorInDoing)
    /\ WF_vars(ErrorInSuper)
    /\ WF_vars(WaiterBlocks)
    /\ WF_vars(WaiterWakes)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* INVARIANTS AND PROPERTIES

\* Liveness: The transaction always reaches a terminal state
TransTerminates ==
    <>(trans_state = "COMPLETED" \/ trans_state = "ABORTED")

\* Liveness: A waiting thread is ALWAYS eventually woken up
\* This proves that btrfs_abort_transaction correctly wakes all waiters
WaiterNeverStuck ==
    (waiter_state = "WAITING") ~> (waiter_state = "WOKEN")

\* Safety: If the transaction aborted, the filesystem MUST be marked as error
AbortSafety ==
    (trans_state = "ABORTED") => (fs_error = TRUE)

=============================================================================
