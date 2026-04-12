-------------------- MODULE BtrfsTransactionTwoStep --------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsTransactionTwoStep.tla — Two-step lock acquisition model
 *
 * This model improves on BtrfsTransaction.tla by splitting every lock
 * check-and-acquire into two separate TLA+ steps:
 *
 *   Step 1 (CHECK): Thread reads the current state and decides to proceed.
 *                   It does NOT yet modify any shared state.
 *   Step 2 (ACT):   Thread re-reads the state and atomically acquires the lock.
 *
 * Between steps 1 and 2, any other thread can run and change the state.
 * This models the real kernel behavior where:
 *   - wait_event(wq, condition) first checks the condition,
 *   - then sleeps if false (other threads run),
 *   - then re-checks when woken up.
 *
 * The key races this exposes that the atomic model misses:
 *
 * RACE 1: "Check-Then-Act on trans_state"
 *   A writer checks trans_state < COMMIT_START (OK to join), gets preempted,
 *   the commit thread advances to COMMIT_START, then the writer wakes up and
 *   joins — violating the blocked_trans_types invariant.
 *
 * RACE 2: "Check-Then-Act on num_extwriters"
 *   The commit thread checks num_extwriters == 0 (OK to advance to DOING),
 *   gets preempted, a new extwriter joins, then the commit thread advances —
 *   violating OnlyCommitterInDoing.
 *
 * RACE 3: "Check-Then-Act on num_writers"
 *   Same as Race 2 but for num_writers.
 *
 * The correct kernel prevents these races via:
 *   - Holding the fs_info->trans_lock spinlock during the check AND the join.
 *   - Using atomic_inc_return for num_writers before the state check.
 *   - The commit thread sets trans_state to COMMIT_START while holding
 *     trans_lock, then waits for extwriters to drain.
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
    \* NEW: two-step state for each writer
    writer_check_state,  \* The state the writer observed during CHECK step
    writer_check_type,   \* The type the writer is trying to join with
    \* NEW: two-step state for commit thread
    commit_check_extwriters, \* extwriters count observed during CHECK
    commit_check_writers,    \* writers count observed during CHECK
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
\* WRITER ACTIONS — TWO STEP

\* Step 1: Writer CHECKS if it can join (reads trans_state, does not modify)
WriterCheckJoin(w, type) ==
    /\ ops_count < MaxOps
    /\ writer_status[w] = "IDLE"
    /\ fs_running_trans = 1
    \* The writer observes the current state
    /\ writer_check_state' = [writer_check_state EXCEPT ![w] = trans_state]
    /\ writer_check_type'  = [writer_check_type  EXCEPT ![w] = type]
    /\ writer_status' = [writer_status EXCEPT ![w] = "CHECKING"]
    /\ ops_count' = ops_count + 1
    /\ UNCHANGED <<fs_running_trans, trans_state, num_writers, num_extwriters,
                   writer_type, commit_check_extwriters, commit_check_writers>>

\* Step 2: Writer ACTS — re-checks and joins. The state may have changed since CHECK.
\* CORRECT VERSION: Re-check the current trans_state, not the cached one.
WriterActJoin(w) ==
    /\ writer_status[w] = "CHECKING"
    /\ fs_running_trans = 1
    \* Re-check with CURRENT state (correct — this is what trans_lock protects)
    /\ \/ (writer_check_type[w] = TYPE_START  /\ trans_state < STATE_COMMIT_START)
       \/ (writer_check_type[w] = TYPE_ATTACH /\ trans_state < STATE_COMMIT_START)
       \/ (writer_check_type[w] = TYPE_JOIN   /\ trans_state < STATE_COMMIT_DOING)
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

\* If the state changed between CHECK and ACT, the writer must retry (go back to IDLE)
WriterRetryJoin(w) ==
    /\ writer_status[w] = "CHECKING"
    \* State changed since we checked — must retry
    /\ \/ (writer_check_type[w] = TYPE_START  /\ trans_state >= STATE_COMMIT_START)
       \/ (writer_check_type[w] = TYPE_ATTACH /\ trans_state >= STATE_COMMIT_START)
       \/ (writer_check_type[w] = TYPE_JOIN   /\ trans_state >= STATE_COMMIT_DOING)
    /\ writer_status' = [writer_status EXCEPT ![w] = "IDLE"]
    /\ writer_check_state' = [writer_check_state EXCEPT ![w] = -1]
    /\ writer_check_type'  = [writer_check_type  EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_running_trans, trans_state, num_writers, num_extwriters,
                   writer_type, ops_count, commit_check_extwriters, commit_check_writers>>

\* Writer leaves the transaction
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

\* Writer initiates a commit
CommitTransaction(w) ==
    /\ writer_status[w] = "RUNNING"
    /\ trans_state = STATE_RUNNING
    /\ writer_status' = [writer_status EXCEPT ![w] = "COMMITTING"]
    /\ trans_state'   = STATE_COMMIT_PREP
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_type,
                   writer_check_state, writer_check_type, ops_count,
                   commit_check_extwriters, commit_check_writers>>

-----------------------------------------------------------------------------
\* COMMIT THREAD ACTIONS — TWO STEP

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

\* Step 1: Commit thread CHECKS num_extwriters and num_writers
CommitCheckForDoing(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_START
    /\ commit_check_extwriters' = num_extwriters
    /\ commit_check_writers'    = num_writers
    /\ writer_status' = [writer_status EXCEPT ![w] = "COMMIT_CHECKING"]
    /\ UNCHANGED <<fs_running_trans, trans_state, num_writers, num_extwriters,
                   writer_type, writer_check_state, writer_check_type, ops_count>>

\* Step 2: Commit thread ACTS — re-checks and advances to DOING
\* CORRECT VERSION: Re-check with current values.
CommitActForDoing(w) ==
    /\ writer_status[w] = "COMMIT_CHECKING"
    /\ trans_state = STATE_COMMIT_START
    \* Re-check with CURRENT values (correct — trans_lock protects this)
    /\ num_extwriters = 0
    /\ num_writers = 1
    /\ trans_state' = STATE_COMMIT_DOING
    /\ writer_status' = [writer_status EXCEPT ![w] = "COMMITTING"]
    /\ commit_check_extwriters' = -1
    /\ commit_check_writers'    = -1
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_type,
                   writer_check_state, writer_check_type, ops_count>>

\* If conditions changed, go back to waiting
CommitRetryForDoing(w) ==
    /\ writer_status[w] = "COMMIT_CHECKING"
    /\ trans_state = STATE_COMMIT_START
    /\ (num_extwriters > 0 \/ num_writers > 1)
    /\ writer_status' = [writer_status EXCEPT ![w] = "COMMITTING"]
    /\ commit_check_extwriters' = -1
    /\ commit_check_writers'    = -1
    /\ UNCHANGED <<fs_running_trans, trans_state, num_writers, num_extwriters,
                   writer_type, writer_check_state, writer_check_type, ops_count>>

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
    \/ \E w \in Writers: WriterRetryJoin(w)
    \/ \E w \in Writers: EndTransaction(w)
    \/ \E w \in Writers: CommitTransaction(w)
    \/ \E w \in Writers: CommitPrepToStart(w)
    \/ \E w \in Writers: CommitCheckForDoing(w)
    \/ \E w \in Writers: CommitActForDoing(w)
    \/ \E w \in Writers: CommitRetryForDoing(w)
    \/ \E w \in Writers: CommitDoingToUnblocked(w)
    \/ \E w \in Writers: CommitUnblockedToSuper(w)
    \/ \E w \in Writers: CommitSuperToCompleted(w)

Fairness ==
    /\ \A w \in Writers: WF_vars(WriterActJoin(w))
    /\ \A w \in Writers: WF_vars(WriterRetryJoin(w))
    /\ \A w \in Writers: WF_vars(EndTransaction(w))
    /\ \A w \in Writers: WF_vars(CommitPrepToStart(w))
    /\ \A w \in Writers: WF_vars(CommitCheckForDoing(w))
    /\ \A w \in Writers: WF_vars(CommitActForDoing(w))
    /\ \A w \in Writers: WF_vars(CommitRetryForDoing(w))
    /\ \A w \in Writers: WF_vars(CommitDoingToUnblocked(w))
    /\ \A w \in Writers: WF_vars(CommitUnblockedToSuper(w))
    /\ \A w \in Writers: WF_vars(CommitSuperToCompleted(w))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* INVARIANTS

NoExtwritersInDoing ==
    (trans_state >= STATE_COMMIT_DOING /\ trans_state < STATE_UNBLOCKED)
        => (num_extwriters = 0)

OnlyCommitterInDoing ==
    (trans_state = STATE_COMMIT_DOING) => (num_writers = 1)

\* NEW: No writer should be CHECKING (between check and act) with a stale cached state
\* that would allow it to join when the current state is blocked.
\* This is the key race: the writer checked OK, but state advanced before it acted.
NoStaleCheckJoin ==
    \A w \in Writers :
        (writer_status[w] = "CHECKING") =>
            \* The writer's cached check_state must still be valid now
            \/ (writer_check_type[w] = TYPE_START  /\ trans_state < STATE_COMMIT_START)
            \/ (writer_check_type[w] = TYPE_ATTACH /\ trans_state < STATE_COMMIT_START)
            \/ (writer_check_type[w] = TYPE_JOIN   /\ trans_state < STATE_COMMIT_DOING)

CommitEventuallyCompletes ==
    (trans_state = STATE_COMMIT_PREP) ~> (trans_state = STATE_COMPLETED)

=============================================================================
