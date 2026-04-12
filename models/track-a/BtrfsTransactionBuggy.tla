----------------------- MODULE BtrfsTransactionBuggy -----------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsTransactionBuggy.tla — Buggy model
 *
 * Models two distinct bugs in the transaction commit state machine:
 *
 * BUG 1: Missing extwriter wait before COMMIT_DOING.
 *   In the correct kernel, the commit thread calls:
 *     wait_event(cur_trans->writer_wait, extwriter_counter_read(cur_trans) == 0)
 *   before transitioning to COMMIT_DOING. This ensures no TRANS_START or
 *   TRANS_ATTACH writers are still active when the commit begins modifying
 *   the extent tree, creating snapshots, and running qgroups.
 *
 *   Without this wait, a TRANS_START writer can be concurrently modifying
 *   the same trees that the commit thread is trying to finalize, causing
 *   silent data corruption (tree node modifications after they have been
 *   written to the commit root).
 *
 *   The bug is: CommitStartToDoing fires even when num_extwriters > 0.
 *
 * BUG 2: New transaction allowed to start before UNBLOCKED.
 *   The correct kernel sets fs_info->running_transaction = NULL only when
 *   transitioning to UNBLOCKED. A buggy implementation that clears it at
 *   COMMIT_DOING would allow a new transaction to start while the old one
 *   is still in COMMIT_DOING, violating the single-active-commit invariant.
 *
 *   The bug is: fs_running_trans is cleared at COMMIT_DOING, not UNBLOCKED.
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
    ops_count

vars == <<fs_running_trans, trans_state, num_writers, num_extwriters,
          writer_status, writer_type, trans2_active, ops_count>>

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
    /\ fs_running_trans = 1
    /\ trans_state      = STATE_RUNNING
    /\ num_writers      = 0
    /\ num_extwriters   = 0
    /\ writer_status    = [w \in Writers |-> "IDLE"]
    /\ writer_type      = [w \in Writers |-> 0]
    /\ trans2_active    = FALSE
    /\ ops_count        = 0

-----------------------------------------------------------------------------
\* WRITER ACTIONS

\* BUG 1: TRANS_START writers can still join even when state = COMMIT_START
\* (because the commit thread doesn't wait for them to drain before DOING)
JoinTransaction(w, type) ==
    /\ ops_count < MaxOps
    /\ writer_status[w] = "IDLE"
    /\ fs_running_trans = 1
    \* BUG 1: TRANS_START is allowed to join up through COMMIT_DOING
    \* (correct model blocks START at COMMIT_START)
    /\ \/ (type = TYPE_START /\ trans_state < STATE_COMMIT_DOING)
       \/ (type = TYPE_ATTACH /\ trans_state < STATE_COMMIT_START)
       \/ (type = TYPE_JOIN /\ trans_state < STATE_COMMIT_DOING)
    /\ writer_status'  = [writer_status EXCEPT ![w] = "RUNNING"]
    /\ writer_type'    = [writer_type EXCEPT ![w] = type]
    /\ num_writers'    = num_writers + 1
    /\ num_extwriters' = IF type \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters + 1
                         ELSE num_extwriters
    /\ ops_count'      = ops_count + 1
    /\ UNCHANGED <<fs_running_trans, trans_state, trans2_active>>

EndTransaction(w) ==
    /\ writer_status[w] = "RUNNING"
    /\ writer_status'  = [writer_status EXCEPT ![w] = "IDLE"]
    /\ num_writers'    = num_writers - 1
    /\ num_extwriters' = IF writer_type[w] \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters - 1
                         ELSE num_extwriters
    /\ writer_type'    = [writer_type EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_running_trans, trans_state, trans2_active, ops_count>>

CommitTransaction(w) ==
    /\ writer_status[w] = "RUNNING"
    /\ trans_state = STATE_RUNNING
    /\ writer_status' = [writer_status EXCEPT ![w] = "COMMITTING"]
    /\ trans_state'   = STATE_COMMIT_PREP
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_type,
                   trans2_active, ops_count>>

CommitPrepToStart(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_PREP
    /\ trans_state' = STATE_COMMIT_START
    /\ num_extwriters' = IF writer_type[w] \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters - 1
                         ELSE num_extwriters
    /\ UNCHANGED <<fs_running_trans, num_writers, writer_status, writer_type,
                   trans2_active, ops_count>>

\* BUG 1: Transition START -> DOING WITHOUT waiting for extwriters == 0
BugCommitStartToDoing(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_START
    \* BUG: no /\ num_extwriters = 0 guard
    \* BUG: no /\ num_writers = 1 guard either — just the committer decides to proceed
    /\ trans_state' = STATE_COMMIT_DOING
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_status, writer_type,
                   trans2_active, ops_count>>

\* BUG 2: Clear running_transaction at DOING (should be UNBLOCKED)
BugCommitDoingToUnblocked(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_DOING
    /\ trans_state' = STATE_UNBLOCKED
    \* BUG: clear running_transaction here instead of waiting for UNBLOCKED
    /\ fs_running_trans' = 0
    /\ UNCHANGED <<num_writers, num_extwriters, writer_status, writer_type,
                   trans2_active, ops_count>>

\* BUG 2: Second transaction starts while first is still in COMMIT_DOING
StartSecondTransaction ==
    /\ fs_running_trans = 0
    /\ ~trans2_active
    /\ trans2_active'    = TRUE
    /\ fs_running_trans' = 1
    /\ UNCHANGED <<trans_state, num_writers, num_extwriters, writer_status, writer_type, ops_count>>

CommitUnblockedToSuper(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_UNBLOCKED
    /\ trans_state' = STATE_SUPER_COMMITTED
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_status, writer_type,
                   trans2_active, ops_count>>

CommitSuperToCompleted(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_SUPER_COMMITTED
    /\ trans_state' = STATE_COMPLETED
    /\ writer_status' = [writer_status EXCEPT ![w] = "IDLE"]
    /\ num_writers' = num_writers - 1
    /\ writer_type' = [writer_type EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_running_trans, num_extwriters, trans2_active, ops_count>>

-----------------------------------------------------------------------------

Next ==
    \/ \E w \in Writers: \E type \in {TYPE_START, TYPE_ATTACH, TYPE_JOIN}: JoinTransaction(w, type)
    \/ \E w \in Writers: EndTransaction(w)
    \/ \E w \in Writers: CommitTransaction(w)
    \/ \E w \in Writers: CommitPrepToStart(w)
    \/ \E w \in Writers: BugCommitStartToDoing(w)
    \/ \E w \in Writers: BugCommitDoingToUnblocked(w)
    \/ StartSecondTransaction
    \/ \E w \in Writers: CommitUnblockedToSuper(w)
    \/ \E w \in Writers: CommitSuperToCompleted(w)

Fairness ==
    /\ \A w \in Writers: WF_vars(EndTransaction(w))
    /\ \A w \in Writers: WF_vars(CommitPrepToStart(w))
    /\ \A w \in Writers: WF_vars(BugCommitStartToDoing(w))
    /\ \A w \in Writers: WF_vars(BugCommitDoingToUnblocked(w))
    /\ \A w \in Writers: WF_vars(CommitUnblockedToSuper(w))
    /\ \A w \in Writers: WF_vars(CommitSuperToCompleted(w))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* INVARIANTS

\* BUG 1 detector: No extwriters should be present in COMMIT_DOING
NoExtwritersInDoing ==
    (trans_state = STATE_COMMIT_DOING) => (num_extwriters = 0)

\* BUG 2 detector: A second transaction must not start while first is in COMMIT_DOING
NoTwoTransactionsInDoing ==
    (trans_state = STATE_COMMIT_DOING) => (~trans2_active)

=============================================================================
