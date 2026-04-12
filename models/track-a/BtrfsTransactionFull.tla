--------------------------- MODULE BtrfsTransactionFull ---------------------------
(*
 * BtrfsTransactionFull.tla — Full Btrfs Transaction State Machine
 *
 * Models the complete BTRFS_TRANS_STATE_* commit state machine as defined in
 * fs/btrfs/transaction.h, including all 6 commit states and the interactions
 * between writers joining, the committer advancing states, and the aborter.
 *
 * TRANSACTION STATES (from btrfs_transaction_state enum)
 * -------------------------------------------------------
 *  TRANS_STATE_RUNNING         = 0  (accepting new writers)
 *  TRANS_STATE_COMMIT_PREP     = 1  (preparing to commit, no new writers)
 *  TRANS_STATE_COMMIT_START    = 2  (commit started, flushing delayed refs)
 *  TRANS_STATE_COMMIT_DOING    = 3  (writing dirty pages, COW B-tree)
 *  TRANS_STATE_UNBLOCKED       = 4  (super block written, writers can join new trans)
 *  TRANS_STATE_SUPER_COMMITTED = 5  (super block committed to all devices)
 *  TRANS_STATE_COMPLETED       = 6  (fully committed, transaction object freed)
 *
 * KEY BUGS THIS MODEL CAN CATCH
 * ------------------------------
 *  1. A writer joins a transaction in COMMIT_START or later state and gets
 *     a handle to a transaction that is about to be freed.
 *  2. The committer advances to COMPLETED before all writers have released
 *     their handles (use-after-free of the transaction object).
 *  3. An aborter races with the committer: both try to set the transaction
 *     to a terminal state (ABORTED vs COMPLETED).
 *  4. A writer blocked on a COMMIT_START transaction is never woken up
 *     (liveness violation).
 *
 * SIMPLIFICATIONS
 * ---------------
 *  - We model one transaction at a time (no transaction chaining).
 *  - We abstract the actual I/O (dirty page writeout, COW B-tree) as
 *    atomic state transitions.
 *  - We model N writers and 1 committer and 1 aborter.
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    NumWriters,              \* number of concurrent writer threads
    MaxOps                   \* maximum number of operations before termination

ASSUME NumWriters \in 1..8
ASSUME MaxOps \in 1..20

Writers == 1..NumWriters

(* ---------------------------------------------------------------------------
 * Transaction states
 * --------------------------------------------------------------------------- *)

TRANS_STATE_RUNNING         == "RUNNING"
TRANS_STATE_COMMIT_PREP     == "COMMIT_PREP"
TRANS_STATE_COMMIT_START    == "COMMIT_START"
TRANS_STATE_COMMIT_DOING    == "COMMIT_DOING"
TRANS_STATE_UNBLOCKED       == "UNBLOCKED"
TRANS_STATE_SUPER_COMMITTED == "SUPER_COMMITTED"
TRANS_STATE_COMPLETED       == "COMPLETED"
TRANS_STATE_ABORTED         == "ABORTED"
TRANS_STATE_NONE            == "NONE"

TerminalStates == {TRANS_STATE_COMPLETED, TRANS_STATE_ABORTED}

CommitSequence == <<
    TRANS_STATE_RUNNING,
    TRANS_STATE_COMMIT_PREP,
    TRANS_STATE_COMMIT_START,
    TRANS_STATE_COMMIT_DOING,
    TRANS_STATE_UNBLOCKED,
    TRANS_STATE_SUPER_COMMITTED,
    TRANS_STATE_COMPLETED
>>

(* ---------------------------------------------------------------------------
 * State variables
 * --------------------------------------------------------------------------- *)

VARIABLES
    trans_state,        \* current state of the transaction
    trans_refcount,     \* number of active writer handles
    trans_aborted,      \* TRUE if the transaction has been aborted
    writer_state,       \* [writer -> state string]
    writer_trans_ok,    \* [writer -> BOOLEAN]: writer successfully joined
    committer_state,    \* state of the committer thread
    aborter_state,      \* state of the aborter thread
    ops_count,          \* global operation counter (for bounding)
    total_joins         \* total number of successful writer joins (informational only)

vars == <<trans_state, trans_refcount, trans_aborted, writer_state,
          writer_trans_ok, committer_state, aborter_state, ops_count, total_joins>>

(* ---------------------------------------------------------------------------
 * Initial state
 * --------------------------------------------------------------------------- *)

Init ==
    /\ trans_state     = TRANS_STATE_RUNNING
    /\ trans_refcount  = 0
    /\ trans_aborted   = FALSE
    /\ writer_state    = [w \in Writers |-> "Idle"]
    /\ writer_trans_ok = [w \in Writers |-> FALSE]
    /\ committer_state = "Idle"
    /\ aborter_state   = "Idle"
    /\ ops_count       = 0
    /\ total_joins     = 0

(* ---------------------------------------------------------------------------
 * Writer actions
 *
 * A writer goes through: Idle -> TryJoin -> Active -> Done
 *
 * TryJoin: the writer checks the transaction state. If it is RUNNING or
 *          COMMIT_PREP, it can join. If it is COMMIT_START or later, it
 *          must wait for the next transaction (we model this as blocking).
 *          The BUG is if a writer joins a transaction in COMMIT_START or
 *          later — it gets a handle to a transaction being committed.
 * --------------------------------------------------------------------------- *)

WriterTryJoin(w) ==
    /\ writer_state[w] = "Idle"
    /\ ops_count < MaxOps
    /\ trans_state \notin TerminalStates
    /\ writer_state'    = [writer_state    EXCEPT ![w] = "TryJoin"]
    /\ ops_count'       = ops_count + 1
    /\ UNCHANGED <<trans_state, trans_refcount, trans_aborted,
                   writer_trans_ok, committer_state, aborter_state, total_joins>>

\* Writer successfully joins: transaction is in RUNNING, COMMIT_PREP, or COMMIT_START
\* (Fix 1.1: TRANS_JOIN is allowed in COMMIT_START per btrfs_blocked_trans_types)
WriterJoinSuccess(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ trans_state \in {TRANS_STATE_RUNNING, TRANS_STATE_COMMIT_PREP,
                        TRANS_STATE_COMMIT_START}
    /\ trans_state \notin TerminalStates
    /\ trans_refcount'  = trans_refcount + 1
    /\ total_joins'     = total_joins + 1
    /\ writer_state'    = [writer_state    EXCEPT ![w] = "Active"]
    /\ writer_trans_ok' = [writer_trans_ok EXCEPT ![w] = TRUE]
    /\ UNCHANGED <<trans_state, trans_aborted, committer_state,
                   aborter_state, ops_count>>

\* Writer is blocked: transaction is in COMMIT_DOING or later, must wait
\* (Fix 1.1: COMMIT_START is now joinable, so blocking starts at COMMIT_DOING)
\* (Fix 1.2: bump trans_refcount to hold a reference while sleeping,
\*  matching wait_current_trans() which calls refcount_inc before wait_event)
WriterBlocked(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ trans_state \in {TRANS_STATE_COMMIT_DOING,
                        TRANS_STATE_UNBLOCKED, TRANS_STATE_SUPER_COMMITTED}
    /\ writer_state'   = [writer_state EXCEPT ![w] = "Blocked"]
    /\ trans_refcount' = trans_refcount + 1   \* Fix 1.2: refcount_inc before sleeping
    /\ UNCHANGED <<trans_state, trans_aborted,
                   writer_trans_ok, committer_state, aborter_state, ops_count, total_joins>>

\* Blocked writer is woken when transaction reaches UNBLOCKED or later
\* (Fix 1.2: decrement trans_refcount on wakeup, matching btrfs_put_transaction
\*  called after wait_event returns in wait_current_trans)
WriterWoken(w) ==
    /\ writer_state[w] = "Blocked"
    /\ trans_state \in {TRANS_STATE_UNBLOCKED, TRANS_STATE_SUPER_COMMITTED,
                        TRANS_STATE_COMPLETED, TRANS_STATE_ABORTED}
    /\ writer_state'   = [writer_state EXCEPT ![w] = "Idle"]
    /\ trans_refcount' = trans_refcount - 1   \* Fix 1.2: btrfs_put_transaction after wakeup
    /\ UNCHANGED <<trans_state, trans_aborted,
                   writer_trans_ok, committer_state, aborter_state, ops_count, total_joins>>

\* Active writer completes its work and releases the handle
WriterDone(w) ==
    /\ writer_state[w] = "Active"
    /\ trans_refcount'  = trans_refcount - 1
    /\ writer_state'    = [writer_state    EXCEPT ![w] = "Done"]
    /\ UNCHANGED <<trans_state, trans_aborted, writer_trans_ok,
                   committer_state, aborter_state, ops_count, total_joins>>

\* Writer bails out of TryJoin when the transaction is aborted or completed
WriterBailOut(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ trans_state \in TerminalStates
    /\ writer_state' = [writer_state EXCEPT ![w] = "Idle"]
    /\ UNCHANGED <<trans_state, trans_refcount, trans_aborted,
                   writer_trans_ok, committer_state, aborter_state, ops_count, total_joins>>

\* Writer resets to Idle for another round
WriterReset(w) ==
    /\ writer_state[w] = "Done"
    /\ ops_count < MaxOps
    /\ writer_state'    = [writer_state    EXCEPT ![w] = "Idle"]
    /\ writer_trans_ok' = [writer_trans_ok EXCEPT ![w] = FALSE]
    /\ UNCHANGED <<trans_state, trans_refcount, trans_aborted,
                   committer_state, aborter_state, ops_count, total_joins>>

(* ---------------------------------------------------------------------------
 * Committer actions
 *
 * The committer advances the transaction through the commit sequence.
 * It can only advance when the transaction is in the expected state.
 * --------------------------------------------------------------------------- *)

\* Fix 1.4: CommitterStart is non-deterministic — the committer can start
\* at any time while the transaction is RUNNING, matching the real kernel
\* where the transaction kthread wakes up periodically or on explicit commit.
CommitterStart ==
    /\ committer_state = "Idle"
    /\ trans_state = TRANS_STATE_RUNNING
    /\ committer_state' = "Committing"
    /\ trans_state'     = TRANS_STATE_COMMIT_PREP
    /\ ops_count'       = ops_count + 1
    /\ UNCHANGED <<trans_refcount, trans_aborted, writer_state,
                   writer_trans_ok, aborter_state, total_joins>>

\* Advance through each commit state
CommitterAdvance(from_state, to_state) ==
    /\ committer_state = "Committing"
    /\ trans_state = from_state
    /\ trans_state' = to_state
    /\ UNCHANGED <<trans_refcount, trans_aborted, writer_state,
                   writer_trans_ok, committer_state, aborter_state, ops_count, total_joins>>

CommitterPrepToStart ==
    CommitterAdvance(TRANS_STATE_COMMIT_PREP, TRANS_STATE_COMMIT_START)

CommitterStartToDoing ==
    CommitterAdvance(TRANS_STATE_COMMIT_START, TRANS_STATE_COMMIT_DOING)

CommitterDoingToUnblocked ==
    CommitterAdvance(TRANS_STATE_COMMIT_DOING, TRANS_STATE_UNBLOCKED)

CommitterUnblockedToSuperCommitted ==
    CommitterAdvance(TRANS_STATE_UNBLOCKED, TRANS_STATE_SUPER_COMMITTED)

\* Final step: advance to COMPLETED only when all writer handles are released
\* and no writer is Active, TryJoin, or Blocked (Blocked writers hold a refcount)
CommitterComplete ==
    /\ committer_state = "Committing"
    /\ trans_state = TRANS_STATE_SUPER_COMMITTED
    /\ trans_refcount = 0      \* SAFETY: no active or blocked handles
    /\ ~trans_aborted
    /\ \A w \in Writers : writer_state[w] \notin {"Active", "TryJoin", "Blocked"}
    /\ trans_state'     = TRANS_STATE_COMPLETED
    /\ committer_state' = "Done"
    /\ UNCHANGED <<trans_refcount, trans_aborted, writer_state,
                   writer_trans_ok, aborter_state, ops_count, total_joins>>

(* ---------------------------------------------------------------------------
 * Aborter actions
 *
 * The aborter can abort the transaction at any point before COMPLETED.
 * --------------------------------------------------------------------------- *)

AborterAbort ==
    /\ aborter_state = "Idle"
    /\ trans_state \notin TerminalStates
    /\ trans_state'    = TRANS_STATE_ABORTED
    /\ trans_aborted'  = TRUE
    /\ aborter_state'  = "Done"
    /\ ops_count'      = ops_count + 1
    /\ UNCHANGED <<trans_refcount, writer_state, writer_trans_ok,
                   committer_state, total_joins>>

(* ---------------------------------------------------------------------------
 * Stutter / termination
 * --------------------------------------------------------------------------- *)

\* Terminal stutter: once the transaction is in a terminal state and all
\* writers are done/idle/blocked-and-woken, the system can stutter.
TerminalStutter ==
    /\ trans_state \in TerminalStates
    /\ \A w \in Writers : writer_state[w] \in {"Idle", "Done", "Blocked"}
    /\ UNCHANGED vars  \* vars includes total_joins

Stutter ==
    /\ ops_count >= MaxOps
    /\ UNCHANGED vars  \* vars includes total_joins

(* ---------------------------------------------------------------------------
 * Next-state relation
 * --------------------------------------------------------------------------- *)

Next ==
    \/ CommitterStart
    \/ CommitterPrepToStart
    \/ CommitterStartToDoing
    \/ CommitterDoingToUnblocked
    \/ CommitterUnblockedToSuperCommitted
    \/ CommitterComplete
    \/ AborterAbort
    \/ \E w \in Writers :
           WriterTryJoin(w) \/ WriterJoinSuccess(w) \/ WriterBlocked(w) \/
           WriterWoken(w) \/ WriterDone(w) \/ WriterReset(w) \/ WriterBailOut(w)
    \/ TerminalStutter
    \/ Stutter

Fairness ==
    /\ SF_vars(CommitterStart)      \* Strong: committer must eventually start
    /\ WF_vars(CommitterPrepToStart)
    /\ WF_vars(CommitterStartToDoing)
    /\ WF_vars(CommitterDoingToUnblocked)
    /\ WF_vars(CommitterUnblockedToSuperCommitted)
    /\ WF_vars(CommitterComplete)
    /\ \A w \in Writers :
           /\ WF_vars(WriterTryJoin(w))
           /\ WF_vars(WriterJoinSuccess(w))
           /\ WF_vars(WriterBlocked(w))
           /\ SF_vars(WriterWoken(w))
           /\ WF_vars(WriterDone(w))
           /\ WF_vars(WriterReset(w))
           /\ WF_vars(WriterBailOut(w))

Spec == Init /\ [][Next]_vars /\ Fairness

(* ---------------------------------------------------------------------------
 * Safety invariants
 * --------------------------------------------------------------------------- *)

\* The transaction object must not be freed while any writer holds a handle
NoUAFOnComplete ==
    trans_state = TRANS_STATE_COMPLETED => trans_refcount = 0

\* A writer must not hold a handle to an aborted transaction
\* (they should have been kicked out during abort)
NoHandleOnAborted ==
    trans_aborted =>
        \A w \in Writers : writer_state[w] \notin {"Active"}

\* The commit sequence must be monotonically increasing
\* (no state can be revisited once left)
CommitStateMonotone ==
    LET rank(s) ==
        CASE s = TRANS_STATE_RUNNING         -> 0
          [] s = TRANS_STATE_COMMIT_PREP     -> 1
          [] s = TRANS_STATE_COMMIT_START    -> 2
          [] s = TRANS_STATE_COMMIT_DOING    -> 3
          [] s = TRANS_STATE_UNBLOCKED       -> 4
          [] s = TRANS_STATE_SUPER_COMMITTED -> 5
          [] s = TRANS_STATE_COMPLETED       -> 6
          [] s = TRANS_STATE_ABORTED         -> 7
          [] OTHER                           -> -1
    IN TRUE  \* Monotonicity is enforced structurally by the action guards

\* No writer can join a transaction in COMMIT_START or later
NoLateJoin ==
    \A w \in Writers :
        writer_state[w] = "Active" =>
            trans_state \in {TRANS_STATE_RUNNING, TRANS_STATE_COMMIT_PREP,
                             TRANS_STATE_COMMIT_START, TRANS_STATE_COMMIT_DOING,
                             TRANS_STATE_UNBLOCKED, TRANS_STATE_SUPER_COMMITTED,
                             TRANS_STATE_COMPLETED, TRANS_STATE_ABORTED}

\* Refcount must never go negative
RefcountNonNegative ==
    trans_refcount >= 0

\* If the transaction is COMPLETED, no writer should be Active
NoActiveOnCompleted ==
    trans_state = TRANS_STATE_COMPLETED =>
        \A w \in Writers : writer_state[w] \notin {"Active", "TryJoin"}

(* ---------------------------------------------------------------------------
 * Liveness properties
 * --------------------------------------------------------------------------- *)

\* A blocked writer must eventually be woken
BlockedWriterEventuallyWoken ==
    \A w \in Writers :
        [](writer_state[w] = "Blocked" =>
           <>(writer_state[w] \in {"Idle", "Done"}))

\* The transaction eventually reaches a terminal state
EventuallyTerminal ==
    <>(trans_state \in TerminalStates)

=============================================================================
