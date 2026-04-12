------------------------- MODULE BtrfsTransaction -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsTransaction.tla — Correct model
 *
 * Models the btrfs transaction commit state machine and its interaction
 * with concurrent writers.
 *
 * The commit state machine goes through:
 * RUNNING -> COMMIT_PREP -> COMMIT_START -> COMMIT_DOING -> UNBLOCKED ->
 * SUPER_COMMITTED -> COMPLETED
 *
 * Key mechanisms verified:
 * 1. Writers (TRANS_START, TRANS_JOIN, etc.) are blocked at specific states
 *    according to btrfs_blocked_trans_types.
 * 2. The commit thread waits for num_extwriters == 0 before COMMIT_DOING.
 * 3. The commit thread waits for num_writers == 1 before COMMIT_DOING.
 * 4. A new transaction can be started once the current one reaches UNBLOCKED.
 *)

CONSTANTS
    Writers,    \* Set of writer IDs
    MaxOps      \* Max operations to bound the model

VARIABLES
    \* Global state
    fs_running_trans,
    
    \* Transaction state
    trans_state,
    num_writers,
    num_extwriters,
    
    \* Writer state
    writer_status,    \* "IDLE", "RUNNING", "COMMITTING"
    writer_type,      \* "START", "JOIN", "ATTACH"
    
    ops_count

vars == <<fs_running_trans, trans_state, num_writers, num_extwriters,
          writer_status, writer_type, ops_count>>

\* State constants
STATE_RUNNING         == 0
STATE_COMMIT_PREP     == 1
STATE_COMMIT_START    == 2
STATE_COMMIT_DOING    == 3
STATE_UNBLOCKED       == 4
STATE_SUPER_COMMITTED == 5
STATE_COMPLETED       == 6

\* Type constants
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
    /\ ops_count        = 0

-----------------------------------------------------------------------------
\* WRITER ACTIONS

\* A writer attempts to join the running transaction
JoinTransaction(w, type) ==
    /\ ops_count < MaxOps
    /\ writer_status[w] = "IDLE"
    /\ fs_running_trans = 1
    \* Check if blocked based on type and current state
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
    /\ UNCHANGED <<fs_running_trans, trans_state>>

\* A writer leaves the transaction
EndTransaction(w) ==
    /\ writer_status[w] = "RUNNING"
    /\ writer_status'  = [writer_status EXCEPT ![w] = "IDLE"]
    /\ num_writers'    = num_writers - 1
    /\ num_extwriters' = IF writer_type[w] \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters - 1
                         ELSE num_extwriters
    /\ writer_type'    = [writer_type EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_running_trans, trans_state, ops_count>>

\* A writer initiates a commit
CommitTransaction(w) ==
    /\ writer_status[w] = "RUNNING"
    /\ trans_state = STATE_RUNNING
    /\ writer_status' = [writer_status EXCEPT ![w] = "COMMITTING"]
    /\ trans_state'   = STATE_COMMIT_PREP
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_type, ops_count>>

-----------------------------------------------------------------------------
\* COMMIT THREAD ACTIONS

\* Transition PREP -> START
CommitPrepToStart(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_PREP
    /\ trans_state' = STATE_COMMIT_START
    \* In START, extwriters drop their ref
    /\ num_extwriters' = IF writer_type[w] \in {TYPE_START, TYPE_ATTACH}
                         THEN num_extwriters - 1
                         ELSE num_extwriters
    /\ UNCHANGED <<fs_running_trans, num_writers, writer_status, writer_type, ops_count>>

\* Transition START -> DOING
\* Requires extwriters == 0 and num_writers == 1 (only the committer)
CommitStartToDoing(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_START
    /\ num_extwriters = 0
    /\ num_writers = 1
    /\ trans_state' = STATE_COMMIT_DOING
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_status, writer_type, ops_count>>

\* Transition DOING -> UNBLOCKED
CommitDoingToUnblocked(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_COMMIT_DOING
    /\ trans_state' = STATE_UNBLOCKED
    /\ fs_running_trans' = 0 \* allow new trans to start
    /\ UNCHANGED <<num_writers, num_extwriters, writer_status, writer_type, ops_count>>

\* Transition UNBLOCKED -> SUPER_COMMITTED
CommitUnblockedToSuper(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_UNBLOCKED
    /\ trans_state' = STATE_SUPER_COMMITTED
    /\ UNCHANGED <<fs_running_trans, num_writers, num_extwriters, writer_status, writer_type, ops_count>>

\* Transition SUPER_COMMITTED -> COMPLETED
CommitSuperToCompleted(w) ==
    /\ writer_status[w] = "COMMITTING"
    /\ trans_state = STATE_SUPER_COMMITTED
    /\ trans_state' = STATE_COMPLETED
    /\ writer_status' = [writer_status EXCEPT ![w] = "IDLE"]
    /\ num_writers' = num_writers - 1
    /\ writer_type' = [writer_type EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_running_trans, num_extwriters, ops_count>>

-----------------------------------------------------------------------------

Next ==
    \/ \E w \in Writers: \E type \in {TYPE_START, TYPE_ATTACH, TYPE_JOIN}: JoinTransaction(w, type)
    \/ \E w \in Writers: EndTransaction(w)
    \/ \E w \in Writers: CommitTransaction(w)
    \/ \E w \in Writers: CommitPrepToStart(w)
    \/ \E w \in Writers: CommitStartToDoing(w)
    \/ \E w \in Writers: CommitDoingToUnblocked(w)
    \/ \E w \in Writers: CommitUnblockedToSuper(w)
    \/ \E w \in Writers: CommitSuperToCompleted(w)

Fairness ==
    /\ \A w \in Writers: WF_vars(EndTransaction(w))
    /\ \A w \in Writers: WF_vars(CommitPrepToStart(w))
    /\ \A w \in Writers: WF_vars(CommitStartToDoing(w))
    /\ \A w \in Writers: WF_vars(CommitDoingToUnblocked(w))
    /\ \A w \in Writers: WF_vars(CommitUnblockedToSuper(w))
    /\ \A w \in Writers: WF_vars(CommitSuperToCompleted(w))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* INVARIANTS

\* Safety: When in COMMIT_DOING, no extwriters can be present
NoExtwritersInDoing ==
    (trans_state >= STATE_COMMIT_DOING /\ trans_state < STATE_UNBLOCKED) => (num_extwriters = 0)

\* Safety: When in COMMIT_DOING, only the committer is writing
OnlyCommitterInDoing ==
    (trans_state = STATE_COMMIT_DOING) => (num_writers = 1)

\* Liveness: If a commit starts, it eventually completes
CommitEventuallyCompletes ==
    (trans_state = STATE_COMMIT_PREP) ~> (trans_state = STATE_COMPLETED)

=============================================================================
