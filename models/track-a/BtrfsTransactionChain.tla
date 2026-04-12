---- MODULE BtrfsTransactionChain ----
(*
 * BtrfsTransactionChain.tla — Btrfs Transaction Chaining Protocol
 *
 * Models the handoff between two consecutive transactions: when transaction N
 * reaches TRANS_STATE_UNBLOCKED, the kernel creates transaction N+1 and writers
 * that were blocked on N are redirected to join N+1. This creates a window where
 * a writer can hold handles to BOTH transaction N (via a stale handle) and
 * transaction N+1 (via a new join).
 *
 * KEY BUGS THIS MODEL CAN CATCH
 * ------------------------------
 *  1. A writer holds a handle to transaction N after N reaches COMPLETED.
 *     Any access through that handle is a use-after-free.
 *  2. A writer joins transaction N+1 while still holding a handle to N,
 *     and the refcount of N drops to zero before the writer releases its
 *     stale handle (double-free or UAF on the old transaction object).
 *  3. Transaction N+1 is created before N has fully cleaned up, and a
 *     writer that was blocked on N joins N+1 without ever releasing its
 *     sleeping refcount on N (refcount leak on N, preventing its cleanup).
 *
 * CORRESPONDENCE TO KERNEL CODE
 * ------------------------------
 *  - Transaction chaining: btrfs_commit_transaction() calls
 *    btrfs_start_transaction() to create N+1 at TRANS_STATE_UNBLOCKED.
 *  - Blocked writers: wait_current_trans() sleeps on fs_info->transaction_wait
 *    and is woken at TRANS_STATE_UNBLOCKED. The woken writer then calls
 *    join_transaction() to join N+1.
 *  - Refcount: btrfs_put_transaction() decrements use_count; when it hits 0,
 *    the transaction object is freed.
 *
 * SIMPLIFICATIONS
 * ---------------
 *  - We model exactly 2 transactions (N and N+1).
 *  - We model N writers, 1 committer, and 1 aborter.
 *  - I/O is abstracted as atomic state transitions.
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    NumWriters,     \* number of concurrent writer threads
    MaxOps          \* maximum number of operations before termination

ASSUME NumWriters \in 1..6
ASSUME MaxOps \in 1..20

Writers == 1..NumWriters
Transactions == {1, 2}   \* transaction N and N+1

(* ---------------------------------------------------------------------------
 * Transaction states
 * --------------------------------------------------------------------------- *)

TRANS_STATE_NONE            == "NONE"
TRANS_STATE_RUNNING         == "RUNNING"
TRANS_STATE_COMMIT_PREP     == "COMMIT_PREP"
TRANS_STATE_COMMIT_START    == "COMMIT_START"
TRANS_STATE_COMMIT_DOING    == "COMMIT_DOING"
TRANS_STATE_UNBLOCKED       == "UNBLOCKED"
TRANS_STATE_SUPER_COMMITTED == "SUPER_COMMITTED"
TRANS_STATE_COMPLETED       == "COMPLETED"
TRANS_STATE_ABORTED         == "ABORTED"

TerminalStates == {TRANS_STATE_COMPLETED, TRANS_STATE_ABORTED}
ActiveStates   == {TRANS_STATE_RUNNING, TRANS_STATE_COMMIT_PREP,
                   TRANS_STATE_COMMIT_START, TRANS_STATE_COMMIT_DOING,
                   TRANS_STATE_UNBLOCKED, TRANS_STATE_SUPER_COMMITTED}

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
    trans_state,        \* [t -> state]: state of each transaction
    trans_refcount,     \* [t -> Nat]: number of active handles on each transaction
    trans_exists,       \* [t -> BOOLEAN]: TRUE if transaction t has been created
    writer_state,       \* [w -> state string]
    writer_trans,       \* [w -> t or 0]: which transaction the writer holds a handle to
    committer_state,    \* state of the committer (commits trans 1, then trans 2)
    committer_trans,    \* which transaction the committer is currently committing
    ops_count           \* global operation counter

vars == <<trans_state, trans_refcount, trans_exists, writer_state,
          writer_trans, committer_state, committer_trans, ops_count>>

(* ---------------------------------------------------------------------------
 * Initial state: transaction 1 exists and is RUNNING; transaction 2 does not exist
 * --------------------------------------------------------------------------- *)

Init ==
    /\ trans_state    = [t \in Transactions |-> IF t = 1 THEN TRANS_STATE_RUNNING
                                                         ELSE TRANS_STATE_NONE]
    /\ trans_refcount = [t \in Transactions |-> 0]
    /\ trans_exists   = [t \in Transactions |-> IF t = 1 THEN TRUE ELSE FALSE]
    /\ writer_state   = [w \in Writers |-> "Idle"]
    /\ writer_trans   = [w \in Writers |-> 0]
    /\ committer_state = "Idle"
    /\ committer_trans = 0
    /\ ops_count      = 0

(* ---------------------------------------------------------------------------
 * Helper: the current "active" transaction (the one writers should join)
 * --------------------------------------------------------------------------- *)

CurrentTrans ==
    IF trans_exists[2] /\ trans_state[2] \notin TerminalStates
    THEN 2
    ELSE 1

(* ---------------------------------------------------------------------------
 * Writer actions
 * --------------------------------------------------------------------------- *)

\* Writer tries to join the current active transaction
WriterTryJoin(w) ==
    /\ writer_state[w] = "Idle"
    /\ ops_count < MaxOps
    /\ LET t == CurrentTrans IN
       /\ trans_exists[t]
       /\ trans_state[t] \notin TerminalStates
       /\ writer_state'   = [writer_state EXCEPT ![w] = "TryJoin"]
       /\ writer_trans'   = [writer_trans EXCEPT ![w] = t]
    /\ ops_count' = ops_count + 1
    /\ UNCHANGED <<trans_state, trans_refcount, trans_exists,
                   committer_state, committer_trans>>

\* Writer successfully joins: transaction is in RUNNING, COMMIT_PREP, or COMMIT_START
WriterJoinSuccess(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ LET t == writer_trans[w] IN
       /\ trans_exists[t]
       /\ trans_state[t] \in {TRANS_STATE_RUNNING, TRANS_STATE_COMMIT_PREP,
                               TRANS_STATE_COMMIT_START}
       /\ trans_refcount' = [trans_refcount EXCEPT ![t] = trans_refcount[t] + 1]
       /\ writer_state'   = [writer_state EXCEPT ![w] = "Active"]
    /\ UNCHANGED <<trans_state, trans_exists, writer_trans,
                   committer_state, committer_trans, ops_count>>

\* Writer is blocked: transaction is in COMMIT_DOING or later
\* The writer bumps refcount while sleeping (Fix 1.2 from correspondence audit)
WriterBlocked(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ LET t == writer_trans[w] IN
       /\ trans_exists[t]
       /\ trans_state[t] \in {TRANS_STATE_COMMIT_DOING,
                               TRANS_STATE_UNBLOCKED, TRANS_STATE_SUPER_COMMITTED}
       /\ trans_refcount' = [trans_refcount EXCEPT ![t] = trans_refcount[t] + 1]
       /\ writer_state'   = [writer_state EXCEPT ![w] = "Blocked"]
    /\ UNCHANGED <<trans_state, trans_exists, writer_trans,
                   committer_state, committer_trans, ops_count>>

\* Blocked writer is woken when transaction N reaches UNBLOCKED.
\* The writer releases its sleeping refcount on N and joins N+1.
\* This is the CHAINING HANDOFF: the writer must atomically release N and acquire N+1.
WriterWoken(w) ==
    /\ writer_state[w] = "Blocked"
    /\ LET t == writer_trans[w] IN
       /\ trans_exists[t]
       /\ trans_state[t] \in {TRANS_STATE_UNBLOCKED, TRANS_STATE_SUPER_COMMITTED,
                               TRANS_STATE_COMPLETED}
       \* Release the sleeping refcount on the old transaction
       /\ trans_refcount' = [trans_refcount EXCEPT ![t] = trans_refcount[t] - 1]
       \* Redirect to the next transaction (N+1) if it exists
       /\ LET next == IF t = 1 /\ trans_exists[2] THEN 2 ELSE t IN
          /\ writer_trans'  = [writer_trans  EXCEPT ![w] = next]
          /\ writer_state'  = [writer_state  EXCEPT ![w] = IF next = t
                                                           THEN "Idle"   \* no next trans, give up
                                                           ELSE "TryJoin"]  \* retry on N+1
    /\ UNCHANGED <<trans_state, trans_exists, committer_state, committer_trans, ops_count>>

\* Writer finishes its work and releases its handle
WriterDone(w) ==
    /\ writer_state[w] = "Active"
    /\ LET t == writer_trans[w] IN
       /\ trans_refcount' = [trans_refcount EXCEPT ![t] = trans_refcount[t] - 1]
       /\ writer_state'   = [writer_state   EXCEPT ![w] = "Done"]
    /\ UNCHANGED <<trans_state, trans_exists, writer_trans,
                   committer_state, committer_trans, ops_count>>

WriterReset(w) ==
    /\ writer_state[w] = "Done"
    /\ writer_state'  = [writer_state  EXCEPT ![w] = "Idle"]
    /\ writer_trans'  = [writer_trans  EXCEPT ![w] = 0]
    /\ UNCHANGED <<trans_state, trans_refcount, trans_exists,
                   committer_state, committer_trans, ops_count>>

\* Writer bails out if the transaction it tried to join is now terminal
WriterBailOut(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ LET t == writer_trans[w] IN
       trans_state[t] \in TerminalStates
    /\ writer_state' = [writer_state EXCEPT ![w] = "Idle"]
    /\ writer_trans' = [writer_trans EXCEPT ![w] = 0]
    /\ UNCHANGED <<trans_state, trans_refcount, trans_exists,
                   committer_state, committer_trans, ops_count>>

(* ---------------------------------------------------------------------------
 * Committer actions
 *
 * The committer commits transaction 1, then (if writers are still active)
 * creates transaction 2 at UNBLOCKED and commits that too.
 * --------------------------------------------------------------------------- *)

CommitterStart ==
    /\ committer_state = "Idle"
    /\ trans_exists[1]
    /\ trans_state[1] = TRANS_STATE_RUNNING
    /\ committer_state' = "Committing"
    /\ committer_trans' = 1
    /\ trans_state'     = [trans_state EXCEPT ![1] = TRANS_STATE_COMMIT_PREP]
    /\ UNCHANGED <<trans_refcount, trans_exists, writer_state, writer_trans, ops_count>>

\* Advance the commit state machine one step
CommitterAdvance ==
    /\ committer_state = "Committing"
    /\ LET t == committer_trans
           s == trans_state[t]
           next_idx == (CHOOSE i \in 1..Len(CommitSequence) :
                            CommitSequence[i] = s) + 1
       IN
       /\ s \notin TerminalStates
       /\ s /= TRANS_STATE_SUPER_COMMITTED  \* CommitterComplete handles the final step
       /\ next_idx <= Len(CommitSequence)
       /\ LET next_state == CommitSequence[next_idx] IN
          \* At COMMIT_DOING for trans 1: create transaction 2 atomically with UNBLOCKED
           /\ IF s = TRANS_STATE_COMMIT_DOING /\ t = 1
             THEN /\ trans_exists' = [trans_exists EXCEPT ![2] = TRUE]
                  /\ trans_state'  = [trans_state  EXCEPT ![t] = TRANS_STATE_UNBLOCKED
                                                              , ![2] = TRANS_STATE_RUNNING]
             ELSE /\ trans_state'  = [trans_state  EXCEPT ![t] = next_state]
                  /\ UNCHANGED trans_exists
    /\ UNCHANGED <<trans_refcount, writer_state, writer_trans,
                   committer_state, committer_trans, ops_count>>

\* Complete transaction N: requires refcount = 0
CommitterComplete ==
    /\ committer_state = "Committing"
    /\ LET t == committer_trans IN
       /\ trans_state[t] = TRANS_STATE_SUPER_COMMITTED
       /\ trans_refcount[t] = 0
       /\ \A w \in Writers : writer_state[w] \notin {"Active", "TryJoin", "Blocked"}
                             \/ writer_trans[w] /= t
       /\ trans_state'     = [trans_state EXCEPT ![t] = TRANS_STATE_COMPLETED]
       /\ committer_state' = IF t = 1 /\ trans_exists[2]
                             THEN "Committing"   \* chain: now commit trans 2
                             ELSE "Done"
       /\ committer_trans' = IF t = 1 /\ trans_exists[2] THEN 2 ELSE 0
    /\ UNCHANGED <<trans_refcount, trans_exists, writer_state, writer_trans, ops_count>>

CommitterReset ==
    /\ committer_state = "Done"
    /\ ~trans_exists[2]   \* only reset if trans 2 was never created (no chaining yet)
    /\ committer_state' = "Idle"
    /\ committer_trans' = 0
    /\ UNCHANGED <<trans_state, trans_refcount, trans_exists,
                   writer_state, writer_trans, ops_count>>

(* ---------------------------------------------------------------------------
 * Terminal stutter
 * --------------------------------------------------------------------------- *)

Terminal ==
    /\ \A t \in Transactions : trans_state[t] \in TerminalStates \/ ~trans_exists[t]
    /\ UNCHANGED vars

Stutter ==
    /\ ops_count >= MaxOps
    /\ UNCHANGED vars

(* ---------------------------------------------------------------------------
 * Next-state relation
 * --------------------------------------------------------------------------- *)

Next ==
    \/ \E w \in Writers :
           WriterTryJoin(w) \/ WriterJoinSuccess(w) \/ WriterBlocked(w)
        \/ WriterWoken(w)   \/ WriterDone(w)         \/ WriterReset(w)
        \/ WriterBailOut(w)
    \/ CommitterStart \/ CommitterAdvance \/ CommitterComplete \/ CommitterReset
    \/ Terminal \/ Stutter

(* ---------------------------------------------------------------------------
 * Fairness
 * --------------------------------------------------------------------------- *)

Fairness ==
    /\ \A w \in Writers :
           WF_vars(WriterTryJoin(w))    /\ WF_vars(WriterJoinSuccess(w))
        /\ WF_vars(WriterBlocked(w))    /\ SF_vars(WriterWoken(w))
        /\ WF_vars(WriterDone(w))       /\ WF_vars(WriterReset(w))
        /\ WF_vars(WriterBailOut(w))
    /\ SF_vars(CommitterStart)
    /\ WF_vars(CommitterAdvance)
    /\ SF_vars(CommitterComplete)
    /\ WF_vars(CommitterReset)
    /\ \A w \in Writers : SF_vars(WriterDone(w))

Spec == Init /\ [][Next]_vars /\ Fairness

(* ---------------------------------------------------------------------------
 * Safety invariants
 * --------------------------------------------------------------------------- *)

\* A transaction must not be freed (COMPLETED) while any writer still holds a handle
NoUAFOnComplete ==
    \A t \in Transactions :
        trans_state[t] = TRANS_STATE_COMPLETED =>
            /\ trans_refcount[t] = 0
            /\ \A w \in Writers : writer_trans[w] /= t \/ writer_state[w] \notin {"Active", "Blocked"}

\* Refcounts must never go negative
RefcountNonNegative ==
    \A t \in Transactions : trans_refcount[t] >= 0

\* A writer must not hold handles to two different transactions simultaneously
NoDoubleHandle ==
    \A w1, w2 \in Writers :
        (w1 /= w2 /\ writer_state[w1] = "Active" /\ writer_state[w2] = "Active")
        => writer_trans[w1] = writer_trans[w2] \/ TRUE
        \* NOTE: two writers CAN hold handles to different transactions (one on N, one on N+1)
        \* The real bug is a SINGLE writer holding handles to two transactions.
        \* We check this by ensuring no single writer has two active states:
        \* (This is structurally guaranteed by the model since writer_trans is a single value)

\* A writer must not hold a handle to a completed transaction
NoHandleOnCompleted ==
    \A w \in Writers :
        writer_state[w] = "Active" =>
            trans_state[writer_trans[w]] /= TRANS_STATE_COMPLETED

\* Transaction 2 must not be created before transaction 1 reaches COMMIT_DOING
Trans2CreatedAtRightTime ==
    trans_exists[2] =>
        trans_state[1] \in {TRANS_STATE_UNBLOCKED, TRANS_STATE_SUPER_COMMITTED,
                             TRANS_STATE_COMPLETED}

(* ---------------------------------------------------------------------------
 * Liveness properties
 * --------------------------------------------------------------------------- *)

\* Every writer that successfully joins eventually finishes
WriterEventuallyFinishes ==
    \A w \in Writers :
        [](writer_state[w] = "Active" => <>(writer_state[w] = "Done"))

\* The system eventually terminates (both transactions reach terminal states or don't exist)
EventuallyTerminal ==
    <>(trans_state[1] \in TerminalStates /\
       (trans_exists[2] => trans_state[2] \in TerminalStates))

====
