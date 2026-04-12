---- MODULE BtrfsTransactionConcrete ----
(*
 * Model: Concrete Btrfs Transaction Chaining
 *
 * This model is a detailed representation of fs/btrfs/transaction.c
 * btrfs_commit_transaction, btrfs_start_transaction, and wait_current_trans.
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS NumWriters, MaxOps

Writers == 1..NumWriters
Transactions == {1, 2}

VARIABLES
    \* Concrete transaction state
    trans_state,        \* [t -> state string]
    trans_use_count,    \* atomic_t use_count
    trans_allocated,    \* BOOLEAN (is the object allocated?)
    
    \* Concrete thread state
    writer_state,       \* [w -> state string]
    writer_trans,       \* pointer to transaction object (1 or 2, or 0)
    
    \* Committer state
    committer_state,
    committer_trans,
    
    ops_count

vars == <<trans_state, trans_use_count, trans_allocated, writer_state,
          writer_trans, committer_state, committer_trans, ops_count>>

Init ==
    /\ trans_state     = [t \in Transactions |-> IF t = 1 THEN "RUNNING" ELSE "NONE"]
    /\ trans_use_count = [t \in Transactions |-> 0]
    /\ trans_allocated = [t \in Transactions |-> IF t = 1 THEN TRUE ELSE FALSE]
    /\ writer_state    = [w \in Writers |-> "Idle"]
    /\ writer_trans    = [w \in Writers |-> 0]
    /\ committer_state = "Idle"
    /\ committer_trans = 0
    /\ ops_count       = 0

CurrentTrans ==
    IF trans_allocated[2] /\ trans_state[2] \notin {"COMPLETED", "ABORTED"}
    THEN 2
    ELSE 1

\* btrfs_start_transaction
WriterTryJoin(w) ==
    /\ writer_state[w] = "Idle"
    /\ ops_count < MaxOps
    /\ LET t == CurrentTrans IN
       /\ trans_allocated[t]
       /\ trans_state[t] \notin {"COMPLETED", "ABORTED"}
       /\ writer_state' = [writer_state EXCEPT ![w] = "TryJoin"]
       /\ writer_trans' = [writer_trans EXCEPT ![w] = t]
    /\ ops_count' = ops_count + 1
    /\ UNCHANGED <<trans_state, trans_use_count, trans_allocated, committer_state, committer_trans>>

\* join_transaction (fast path)
WriterJoinSuccess(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ LET t == writer_trans[w] IN
       /\ trans_allocated[t]
       /\ trans_state[t] \in {"RUNNING", "COMMIT_PREP", "COMMIT_START"}
       /\ trans_use_count' = [trans_use_count EXCEPT ![t] = trans_use_count[t] + 1]
       /\ writer_state' = [writer_state EXCEPT ![w] = "Active"]
    /\ UNCHANGED <<trans_state, trans_allocated, writer_trans, committer_state, committer_trans, ops_count>>

\* wait_current_trans (blocks)
WriterBlocked(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ LET t == writer_trans[w] IN
       /\ trans_allocated[t]
       /\ trans_state[t] \in {"COMMIT_DOING", "UNBLOCKED", "SUPER_COMMITTED"}
       /\ trans_use_count' = [trans_use_count EXCEPT ![t] = trans_use_count[t] + 1]
       /\ writer_state' = [writer_state EXCEPT ![w] = "Blocked"]
    /\ UNCHANGED <<trans_state, trans_allocated, writer_trans, committer_state, committer_trans, ops_count>>

\* wake_up(&fs_info->transaction_wait)
WriterWoken(w) ==
    /\ writer_state[w] = "Blocked"
    /\ LET t == writer_trans[w] IN
       /\ trans_allocated[t]
       /\ trans_state[t] \in {"UNBLOCKED", "SUPER_COMMITTED", "COMPLETED"}
       /\ trans_use_count' = [trans_use_count EXCEPT ![t] = trans_use_count[t] - 1]
       /\ LET next == IF t = 1 /\ trans_allocated[2] THEN 2 ELSE t IN
          /\ writer_trans' = [writer_trans EXCEPT ![w] = next]
          /\ writer_state' = [writer_state EXCEPT ![w] = IF next = t THEN "Idle" ELSE "TryJoin"]
    /\ UNCHANGED <<trans_state, trans_allocated, committer_state, committer_trans, ops_count>>

\* btrfs_end_transaction
WriterDone(w) ==
    /\ writer_state[w] = "Active"
    /\ LET t == writer_trans[w] IN
       /\ trans_use_count' = [trans_use_count EXCEPT ![t] = trans_use_count[t] - 1]
       /\ writer_state' = [writer_state EXCEPT ![w] = "Done"]
    /\ UNCHANGED <<trans_state, trans_allocated, writer_trans, committer_state, committer_trans, ops_count>>

WriterReset(w) ==
    /\ writer_state[w] = "Done"
    /\ writer_state' = [writer_state EXCEPT ![w] = "Idle"]
    /\ writer_trans' = [writer_trans EXCEPT ![w] = 0]
    /\ UNCHANGED <<trans_state, trans_use_count, trans_allocated, committer_state, committer_trans, ops_count>>

WriterBailOut(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ LET t == writer_trans[w] IN
       trans_state[t] \in {"COMPLETED", "ABORTED"}
    /\ writer_state' = [writer_state EXCEPT ![w] = "Idle"]
    /\ writer_trans' = [writer_trans EXCEPT ![w] = 0]
    /\ UNCHANGED <<trans_state, trans_use_count, trans_allocated, committer_state, committer_trans, ops_count>>

\* btrfs_commit_transaction
CommitterStart ==
    /\ committer_state = "Idle"
    /\ trans_allocated[1]
    /\ trans_state[1] = "RUNNING"
    /\ committer_state' = "Committing"
    /\ committer_trans' = 1
    /\ trans_state' = [trans_state EXCEPT ![1] = "COMMIT_PREP"]
    /\ UNCHANGED <<trans_use_count, trans_allocated, writer_state, writer_trans, ops_count>>

CommitSequence == <<
    "RUNNING",
    "COMMIT_PREP",
    "COMMIT_START",
    "COMMIT_DOING",
    "UNBLOCKED",
    "SUPER_COMMITTED",
    "COMPLETED"
>>

CommitterAdvance ==
    /\ committer_state = "Committing"
    /\ LET t == committer_trans
           s == trans_state[t]
           next_idx == (CHOOSE i \in 1..Len(CommitSequence) : CommitSequence[i] = s) + 1
       IN
       /\ s \notin {"COMPLETED", "ABORTED"}
       /\ s /= "SUPER_COMMITTED"
       /\ next_idx <= Len(CommitSequence)
       /\ LET next_state == CommitSequence[next_idx] IN
          /\ IF s = "COMMIT_DOING" /\ t = 1
             THEN /\ trans_allocated' = [trans_allocated EXCEPT ![2] = TRUE]
                  /\ trans_state' = [trans_state EXCEPT ![t] = "UNBLOCKED", ![2] = "RUNNING"]
             ELSE /\ trans_state' = [trans_state EXCEPT ![t] = next_state]
                  /\ UNCHANGED trans_allocated
    /\ UNCHANGED <<trans_use_count, writer_state, writer_trans, committer_state, committer_trans, ops_count>>

CommitterComplete ==
    /\ committer_state = "Committing"
    /\ LET t == committer_trans IN
       /\ trans_state[t] = "SUPER_COMMITTED"
       /\ trans_use_count[t] = 0
       /\ \A w \in Writers : writer_state[w] \notin {"Active", "TryJoin", "Blocked"} \/ writer_trans[w] /= t
       /\ trans_state' = [trans_state EXCEPT ![t] = "COMPLETED"]
       /\ committer_state' = IF t = 1 /\ trans_allocated[2] THEN "Committing" ELSE "Done"
       /\ committer_trans' = IF t = 1 /\ trans_allocated[2] THEN 2 ELSE 0
    /\ UNCHANGED <<trans_use_count, trans_allocated, writer_state, writer_trans, ops_count>>

CommitterReset ==
    /\ committer_state = "Done"
    /\ ~trans_allocated[2]
    /\ committer_state' = "Idle"
    /\ committer_trans' = 0
    /\ UNCHANGED <<trans_state, trans_use_count, trans_allocated, writer_state, writer_trans, ops_count>>

Terminal ==
    /\ \A t \in Transactions : trans_state[t] \in {"COMPLETED", "ABORTED"} \/ ~trans_allocated[t]
    /\ UNCHANGED vars

Stutter ==
    /\ ops_count >= MaxOps
    /\ UNCHANGED vars

Next ==
    \/ \E w \in Writers : WriterTryJoin(w) \/ WriterJoinSuccess(w) \/ WriterBlocked(w)
        \/ WriterWoken(w) \/ WriterDone(w) \/ WriterReset(w) \/ WriterBailOut(w)
    \/ CommitterStart \/ CommitterAdvance \/ CommitterComplete \/ CommitterReset
    \/ Terminal \/ Stutter

Fairness ==
    /\ \A w \in Writers :
           WF_vars(WriterTryJoin(w)) /\ WF_vars(WriterJoinSuccess(w))
        /\ WF_vars(WriterBlocked(w)) /\ SF_vars(WriterWoken(w))
        /\ WF_vars(WriterDone(w)) /\ WF_vars(WriterReset(w))
        /\ WF_vars(WriterBailOut(w))
    /\ SF_vars(CommitterStart)
    /\ WF_vars(CommitterAdvance)
    /\ SF_vars(CommitterComplete)
    /\ WF_vars(CommitterReset)
    /\ \A w \in Writers : SF_vars(WriterDone(w))

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
