---------------------- MODULE BtrfsTransactionBuggy2 ----------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsTransactionBuggy2.tla — Bug 2 only
 *
 * BUG 2: New transaction allowed to start before UNBLOCKED.
 *
 * The correct kernel does:
 *   spin_lock(&fs_info->trans_lock);
 *   cur_trans->state = TRANS_STATE_UNBLOCKED;
 *   fs_info->running_transaction = NULL;   <-- cleared atomically with state change
 *   spin_unlock(&fs_info->trans_lock);
 *
 * A buggy implementation that clears running_transaction BEFORE advancing
 * the state to UNBLOCKED would allow a new transaction to start while the
 * old one is still in COMMIT_DOING. The new transaction's writers would
 * then modify the same extent tree nodes that the old commit is finalizing.
 *
 * We model this by splitting the DOING->UNBLOCKED transition into two steps:
 *   Step 1: Clear fs_running_trans (BUG: while still in DOING)
 *   Step 2: Advance state to UNBLOCKED
 * Between these two steps, StartSecondTransaction can fire.
 *)

CONSTANTS
    Writers,
    MaxOps

VARIABLES
    fs_running_trans,
    trans_state,
    num_writers,
    num_extwriters,
    writer_status,
    writer_type,
    trans2_active,
    \* Intermediate flag: running_trans cleared but state not yet UNBLOCKED
    trans_cleared_early,
    ops_count

vars == <<fs_running_trans, trans_state, num_writers, num_extwriters,
          writer_status, writer_type, trans2_active, trans_cleared_early, ops_count>>

STATE_RUNNING         == 0
STATE_COMMIT_PREP     == 1
STATE_COMMIT_START    == 2
STATE_COMMIT_DOING    == 3
STATE_UNBLOCKED       == 4
STATE_SUPER_COMMITTED == 5
STATE_COMPLETED       == 6

TYPE_START  == 1
TYPE_ATTACH == 2
TYPE_JOIN   == 3

Init ==
    /\ fs_running_trans    = 1
    /\ trans_state         = STATE_RUNNING
    /\ num_writers         = 0
    /\ num_extwriters      = 0
    /\ writer_status       = [w \in Writers |-> "IDLE"]
    /\ writer_type         = [w \in Writers |-> 0]
    /\ trans2_active       = FALSE
    /\ trans_cleared_early = FALSE
    /\ ops_count           = 0

-----------------------------------------------------------------------------

JoinTransaction(w, type) ==
    /\ ops_count < MaxOps
    /\ writer_status[w] = "IDLE"
    /\ fs_running_trans = 1
    /\ \/ (type = TYPE_START /\ trans_state < STATE_COMMIT_START)
       \/ (type = TYPE_ATTACH /\ trans_state < STATE_COMMIT_START)
       \/ (type = TYPE_JOIN /\ trans_state < STATE_COMMIT_DOING)
    /\ writer_status'  = [writer_status EXCEPT ![w] = "RUNNING"]
    /\ writer_type'    = [writer_type EXCEPT ![w] = type]
    /\ num_writers'    = num_writers + 1
    /\ num_extwriters' = IF type \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters + 1
                         ELSE num_extwriters
    /\ ops_count'      = ops_count + 1
    /\ UNCHANGED <<fs_running_trans, trans_state, trans2_active, trans_cleared_early>>

EndTransaction(w) ==
    /\ writer_status[w] = "RUNNING"
    /\ writer_status'  = [writer_status EXCEPT ![w] = "IDLE"]
    /\ num_writers'    = num_writers - 1
    /\ num_extwriters' = IF writer_type[w] \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters - 1
                         ELSE num_extwriters
    /\ writer_type'    = [writer_type EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_running_trans, trans_state, trans2_active, trans_cleared_early, ops_count>>

CommitTransaction(w) ==
    /\ writer_status[w] = "RUNNING"
    /\ trans_state = STATE_RUNNING
    /\ writer_status' = [writer_status EXCEPT ![w] = "COMMITTING"]
    /\ trans_state'   = STATE_COMMIT_PREP
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_type,
                   trans2_active, trans_cleared_early, ops_count>>

CommitPrepToStart(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_PREP
    /\ trans_state' = STATE_COMMIT_START
    /\ num_extwriters' = IF writer_type[w] \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters - 1
                         ELSE num_extwriters
    /\ UNCHANGED <<fs_running_trans, num_writers, writer_status, writer_type,
                   trans2_active, trans_cleared_early, ops_count>>

CommitStartToDoing(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_START
    /\ num_extwriters = 0
    /\ num_writers = 1
    /\ trans_state' = STATE_COMMIT_DOING
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_status, writer_type,
                   trans2_active, trans_cleared_early, ops_count>>

\* BUG 2 Step 1: Commit thread clears running_transaction while still in DOING
\* (In correct code this happens atomically with the UNBLOCKED state transition)
BugClearRunningTrans(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_DOING
    /\ ~trans_cleared_early
    \* BUG: clear running_transaction before advancing state
    /\ fs_running_trans'    = 0
    /\ trans_cleared_early' = TRUE
    /\ UNCHANGED <<trans_state, num_writers, num_extwriters, writer_status, writer_type,
                   trans2_active, ops_count>>

\* BUG 2 Step 2: Now advance to UNBLOCKED (too late — damage already done)
CommitDoingToUnblocked(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_DOING
    /\ trans_cleared_early
    /\ trans_state' = STATE_UNBLOCKED
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_status, writer_type,
                   trans2_active, trans_cleared_early, ops_count>>

\* Second transaction starts when running_trans = 0
\* This fires BETWEEN BugClearRunningTrans and CommitDoingToUnblocked
StartSecondTransaction ==
    /\ fs_running_trans = 0
    /\ ~trans2_active
    /\ trans2_active'    = TRUE
    /\ fs_running_trans' = 1
    /\ UNCHANGED <<trans_state, num_writers, num_extwriters, writer_status, writer_type,
                   trans_cleared_early, ops_count>>

CommitUnblockedToSuper(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_UNBLOCKED
    /\ trans_state' = STATE_SUPER_COMMITTED
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_status, writer_type,
                   trans2_active, trans_cleared_early, ops_count>>

CommitSuperToCompleted(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_SUPER_COMMITTED
    /\ trans_state' = STATE_COMPLETED
    /\ writer_status' = [writer_status EXCEPT ![w] = "IDLE"]
    /\ num_writers' = num_writers - 1
    /\ writer_type' = [writer_type EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_running_trans, num_extwriters, trans2_active, trans_cleared_early, ops_count>>

-----------------------------------------------------------------------------

Next ==
    \/ \E w \in Writers: \E type \in {TYPE_START, TYPE_ATTACH, TYPE_JOIN}: JoinTransaction(w, type)
    \/ \E w \in Writers: EndTransaction(w)
    \/ \E w \in Writers: CommitTransaction(w)
    \/ \E w \in Writers: CommitPrepToStart(w)
    \/ \E w \in Writers: CommitStartToDoing(w)
    \/ \E w \in Writers: BugClearRunningTrans(w)
    \/ StartSecondTransaction
    \/ \E w \in Writers: CommitDoingToUnblocked(w)
    \/ \E w \in Writers: CommitUnblockedToSuper(w)
    \/ \E w \in Writers: CommitSuperToCompleted(w)

Fairness ==
    /\ \A w \in Writers: WF_vars(EndTransaction(w))
    /\ \A w \in Writers: WF_vars(CommitPrepToStart(w))
    /\ \A w \in Writers: WF_vars(CommitStartToDoing(w))
    /\ \A w \in Writers: WF_vars(BugClearRunningTrans(w))
    /\ \A w \in Writers: WF_vars(CommitDoingToUnblocked(w))
    /\ \A w \in Writers: WF_vars(CommitUnblockedToSuper(w))
    /\ \A w \in Writers: WF_vars(CommitSuperToCompleted(w))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* INVARIANTS

\* BUG 2 detector: A second transaction must not start while first is in COMMIT_DOING
NoTwoTransactionsInDoing ==
    (trans_state = STATE_COMMIT_DOING) => (~trans2_active)

=============================================================================
