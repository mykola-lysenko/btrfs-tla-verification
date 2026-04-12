-------------------- MODULE BtrfsTransactionTwoStepBuggy --------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsTransactionTwoStepBuggy.tla — Buggy two-step lock acquisition model
 *
 * THE BUG: The writer uses its STALE CACHED check_state instead of re-checking
 * the current trans_state before joining. This is what happens if the
 * fs_info->trans_lock spinlock is NOT held across the check-and-join sequence.
 *
 * Without the spinlock, the sequence is:
 *   1. Writer reads trans_state (OK to join)
 *   2. Writer gets preempted
 *   3. Commit thread advances trans_state to COMMIT_START
 *   4. Writer wakes up, sees its cached check_state (RUNNING), joins anyway
 *   => Writer is now RUNNING inside a COMMIT_START transaction — violation!
 *
 * Similarly for the commit thread:
 *   1. Commit thread reads num_extwriters = 0 (OK to advance to DOING)
 *   2. Commit thread gets preempted
 *   3. A new extwriter joins (num_extwriters = 1)
 *   4. Commit thread wakes up, sees its cached check (0), advances to DOING
 *   => Extwriter is now RUNNING inside COMMIT_DOING — violation!
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
    writer_check_state,
    writer_check_type,
    commit_check_extwriters,
    commit_check_writers,
    ops_count

vars == <<fs_running_trans, trans_state, num_writers, num_extwriters,
          writer_status, writer_type, writer_check_state, writer_check_type,
          commit_check_extwriters, commit_check_writers, ops_count>>

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
    /\ writer_check_state = [w \in Writers |-> -1]
    /\ writer_check_type  = [w \in Writers |-> 0]
    /\ commit_check_extwriters = -1
    /\ commit_check_writers    = -1
    /\ ops_count        = 0

-----------------------------------------------------------------------------
\* WRITER ACTIONS — BUGGY TWO STEP

WriterCheckJoin(w, type) ==
    /\ ops_count < MaxOps
    /\ writer_status[w] = "IDLE"
    /\ fs_running_trans = 1
    /\ writer_check_state' = [writer_check_state EXCEPT ![w] = trans_state]
    /\ writer_check_type'  = [writer_check_type  EXCEPT ![w] = type]
    /\ writer_status' = [writer_status EXCEPT ![w] = "CHECKING"]
    /\ ops_count' = ops_count + 1
    /\ UNCHANGED <<fs_running_trans, trans_state, num_writers, num_extwriters,
                   writer_type, commit_check_extwriters, commit_check_writers>>

\* BUG: Uses the STALE CACHED check_state instead of re-checking trans_state.
\* No retry path — the writer always acts on its cached observation.
WriterActJoin(w) ==
    /\ writer_status[w] = "CHECKING"
    /\ fs_running_trans = 1
    \* BUG: Use cached writer_check_state[w], NOT current trans_state
    /\ \/ (writer_check_type[w] = TYPE_START  /\ writer_check_state[w] < STATE_COMMIT_START)
       \/ (writer_check_type[w] = TYPE_ATTACH /\ writer_check_state[w] < STATE_COMMIT_START)
       \/ (writer_check_type[w] = TYPE_JOIN   /\ writer_check_state[w] < STATE_COMMIT_DOING)
    /\ writer_status'  = [writer_status EXCEPT ![w] = "RUNNING"]
    /\ writer_type'    = [writer_type EXCEPT ![w] = writer_check_type[w]]
    /\ num_writers'    = num_writers + 1
    /\ num_extwriters' = IF writer_check_type[w] \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters + 1
                         ELSE num_extwriters
    /\ writer_check_state' = [writer_check_state EXCEPT ![w] = -1]
    /\ writer_check_type'  = [writer_check_type  EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_running_trans, trans_state, ops_count,
                   commit_check_extwriters, commit_check_writers>>

EndTransaction(w) ==
    /\ writer_status[w] = "RUNNING"
    /\ writer_status'  = [writer_status EXCEPT ![w] = "IDLE"]
    /\ num_writers'    = num_writers - 1
    /\ num_extwriters' = IF writer_type[w] \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters - 1
                         ELSE num_extwriters
    /\ writer_type'    = [writer_type EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_running_trans, trans_state, ops_count,
                   writer_check_state, writer_check_type,
                   commit_check_extwriters, commit_check_writers>>

CommitTransaction(w) ==
    /\ writer_status[w] = "RUNNING"
    /\ trans_state = STATE_RUNNING
    /\ writer_status' = [writer_status EXCEPT ![w] = "COMMITTING"]
    /\ trans_state'   = STATE_COMMIT_PREP
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_type,
                   writer_check_state, writer_check_type, ops_count,
                   commit_check_extwriters, commit_check_writers>>

-----------------------------------------------------------------------------
\* COMMIT THREAD ACTIONS — BUGGY TWO STEP

CommitPrepToStart(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_PREP
    /\ trans_state' = STATE_COMMIT_START
    /\ num_extwriters' = IF writer_type[w] \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters - 1
                         ELSE num_extwriters
    /\ UNCHANGED <<fs_running_trans, num_writers, writer_status, writer_type,
                   writer_check_state, writer_check_type, ops_count,
                   commit_check_extwriters, commit_check_writers>>

CommitCheckForDoing(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_START
    /\ commit_check_extwriters' = num_extwriters
    /\ commit_check_writers'    = num_writers
    /\ writer_status' = [writer_status EXCEPT ![w] = "COMMIT_CHECKING"]
    /\ UNCHANGED <<fs_running_trans, trans_state, num_writers, num_extwriters,
                   writer_type, writer_check_state, writer_check_type, ops_count>>

\* BUG: Uses stale cached values instead of re-checking current num_extwriters/num_writers
CommitActForDoing(w) ==
    /\ writer_status[w] = "COMMIT_CHECKING"
    /\ trans_state = STATE_COMMIT_START
    \* BUG: Use cached values, not current values
    /\ commit_check_extwriters = 0
    /\ commit_check_writers = 1
    /\ trans_state' = STATE_COMMIT_DOING
    /\ writer_status' = [writer_status EXCEPT ![w] = "COMMITTING"]
    /\ commit_check_extwriters' = -1
    /\ commit_check_writers'    = -1
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_type,
                   writer_check_state, writer_check_type, ops_count>>

CommitDoingToUnblocked(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_DOING
    /\ trans_state' = STATE_UNBLOCKED
    /\ fs_running_trans' = 0
    /\ UNCHANGED <<num_writers, num_extwriters, writer_status, writer_type,
                   writer_check_state, writer_check_type, ops_count,
                   commit_check_extwriters, commit_check_writers>>

CommitUnblockedToSuper(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_UNBLOCKED
    /\ trans_state' = STATE_SUPER_COMMITTED
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_status,
                   writer_type, writer_check_state, writer_check_type, ops_count,
                   commit_check_extwriters, commit_check_writers>>

CommitSuperToCompleted(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_SUPER_COMMITTED
    /\ trans_state' = STATE_COMPLETED
    /\ writer_status' = [writer_status EXCEPT ![w] = "IDLE"]
    /\ num_writers' = num_writers - 1
    /\ writer_type' = [writer_type EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_running_trans, num_extwriters, writer_check_state,
                   writer_check_type, ops_count,
                   commit_check_extwriters, commit_check_writers>>

-----------------------------------------------------------------------------

Next ==
    \/ \E w \in Writers: \E type \in {TYPE_START, TYPE_ATTACH, TYPE_JOIN}:
           WriterCheckJoin(w, type)
    \/ \E w \in Writers: WriterActJoin(w)
    \/ \E w \in Writers: EndTransaction(w)
    \/ \E w \in Writers: CommitTransaction(w)
    \/ \E w \in Writers: CommitPrepToStart(w)
    \/ \E w \in Writers: CommitCheckForDoing(w)
    \/ \E w \in Writers: CommitActForDoing(w)
    \/ \E w \in Writers: CommitDoingToUnblocked(w)
    \/ \E w \in Writers: CommitUnblockedToSuper(w)
    \/ \E w \in Writers: CommitSuperToCompleted(w)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* INVARIANTS

NoExtwritersInDoing ==
    (trans_state >= STATE_COMMIT_DOING /\ trans_state < STATE_UNBLOCKED)
        => (num_extwriters = 0)

OnlyCommitterInDoing ==
    (trans_state = STATE_COMMIT_DOING) => (num_writers = 1)

NoStaleCheckJoin ==
    \A w \in Writers :
        (writer_status[w] = "CHECKING") =>
            \/ (writer_check_type[w] = TYPE_START  /\ trans_state < STATE_COMMIT_START)
            \/ (writer_check_type[w] = TYPE_ATTACH /\ trans_state < STATE_COMMIT_START)
            \/ (writer_check_type[w] = TYPE_JOIN   /\ trans_state < STATE_COMMIT_DOING)

=============================================================================
