------------------------ MODULE BtrfsTransactionUAF ------------------------
EXTENDS Integers, Sequences, TLC

(*
This model demonstrates the fix for the CVE-2025-21753 Use-After-Free bug.
The fix is to read the `aborted` field WHILE still holding the trans_lock,
or to bump the refcount while holding the lock before dropping it.
Here we model bumping the refcount while holding the lock, reading aborted,
then dropping the lock.
*)

CONSTANTS 
    NumWriters,
    MaxTransactions

VARIABLES
    heap_allocated,     \* [1..MaxTransactions -> BOOLEAN]
    heap_refcount,      \* [1..MaxTransactions -> Nat]
    heap_aborted,       \* [1..MaxTransactions -> BOOLEAN]
    running_trans_id,   \* 0 if no running transaction, else 1..MaxTransactions
    trans_lock,         \* BOOLEAN
    writer_state,       \* [1..NumWriters -> {"Idle", "Joining", "Joined", "Done", "Error"}]
    writer_trans_ptr,   \* [1..NumWriters -> Nat] (pointer to heap slot)
    aborter_state       \* {"Idle", "Aborting", "Done"}

vars == <<heap_allocated, heap_refcount, heap_aborted, running_trans_id, trans_lock, writer_state, writer_trans_ptr, aborter_state>>

Init ==
    /\ heap_allocated = [i \in 1..MaxTransactions |-> FALSE]
    /\ heap_refcount = [i \in 1..MaxTransactions |-> 0]
    /\ heap_aborted = [i \in 1..MaxTransactions |-> FALSE]
    /\ running_trans_id = 0
    /\ trans_lock = FALSE
    /\ writer_state = [w \in 1..NumWriters |-> "Idle"]
    /\ writer_trans_ptr = [w \in 1..NumWriters |-> 0]
    /\ aborter_state = "Idle"

\* A background process creates a running transaction if none exists
CreateTransaction ==
    /\ running_trans_id = 0
    /\ \E i \in 1..MaxTransactions : heap_allocated[i] = FALSE
    /\ \E w \in 1..NumWriters : writer_state[w] = "Idle"
    /\ trans_lock = FALSE
    /\ \E new_id \in {i \in 1..MaxTransactions : heap_allocated[i] = FALSE} :
       /\ heap_allocated' = [heap_allocated EXCEPT ![new_id] = TRUE]
       /\ heap_refcount' = [heap_refcount EXCEPT ![new_id] = 1]
       /\ heap_aborted' = [heap_aborted EXCEPT ![new_id] = FALSE]
       /\ running_trans_id' = new_id
    /\ UNCHANGED <<writer_state, writer_trans_ptr, aborter_state, trans_lock>>

\* Writer attempts to join transaction (Correct version)
WriterJoinStep1(w) ==
    /\ writer_state[w] = "Idle"
    /\ trans_lock = FALSE
    /\ running_trans_id /= 0
    /\ writer_trans_ptr' = [writer_trans_ptr EXCEPT ![w] = running_trans_id]
    \* CORRECT FIX: Bump refcount BEFORE dropping the lock!
    /\ heap_refcount' = [heap_refcount EXCEPT ![running_trans_id] = heap_refcount[running_trans_id] + 1]
    /\ writer_state' = [writer_state EXCEPT ![w] = "Joining"]
    /\ UNCHANGED <<heap_allocated, heap_aborted, running_trans_id, aborter_state, trans_lock>>

WriterJoinStep2(w) ==
    /\ writer_state[w] = "Joining"
    \* Reads the aborted field of the transaction it has a pointer to.
    \* Since it holds a refcount, heap_allocated MUST be TRUE.
    /\ Assert(heap_allocated[writer_trans_ptr[w]], "Use-After-Free: Accessing freed transaction object!")
    /\ IF heap_aborted[writer_trans_ptr[w]] THEN
          writer_state' = [writer_state EXCEPT ![w] = "Error"]
       ELSE
          writer_state' = [writer_state EXCEPT ![w] = "Joined"]
    /\ UNCHANGED <<heap_allocated, heap_refcount, heap_aborted, running_trans_id, trans_lock, writer_trans_ptr, aborter_state>>

\* Aborter aborts the current transaction and cleans it up
AborterStep1 ==
    /\ aborter_state = "Idle"
    /\ running_trans_id /= 0
    /\ trans_lock = FALSE
    /\ heap_aborted' = [heap_aborted EXCEPT ![running_trans_id] = TRUE]
    /\ aborter_state' = "Aborting"
    /\ UNCHANGED <<heap_allocated, heap_refcount, running_trans_id, writer_state, writer_trans_ptr, trans_lock>>

AborterStep2 ==
    /\ aborter_state = "Aborting"
    /\ trans_lock = FALSE
    \* Removes it from running
    /\ heap_refcount' = [heap_refcount EXCEPT ![running_trans_id] = heap_refcount[running_trans_id] - 1]
    /\ running_trans_id' = 0
    /\ aborter_state' = "Done"
    /\ UNCHANGED <<heap_allocated, heap_aborted, writer_state, writer_trans_ptr, trans_lock>>

\* Background cleanup process frees objects with 0 refcount
CleanupTransaction ==
    /\ \E id \in 1..MaxTransactions :
       /\ heap_allocated[id] = TRUE /\ heap_refcount[id] = 0
       /\ heap_allocated' = [heap_allocated EXCEPT ![id] = FALSE]
    /\ UNCHANGED <<heap_refcount, heap_aborted, running_trans_id, trans_lock, writer_state, writer_trans_ptr, aborter_state>>

Next == 
    \/ CreateTransaction
    \/ \E w \in 1..NumWriters : WriterJoinStep1(w) \/ WriterJoinStep2(w)
    \/ AborterStep1
    \/ AborterStep2
    \/ CleanupTransaction
    \/ \E w \in 1..NumWriters : 
          /\ writer_state[w] \in {"Joined", "Error"}
          /\ writer_state' = [writer_state EXCEPT ![w] = "Idle"]
          /\ heap_refcount' = [heap_refcount EXCEPT ![writer_trans_ptr[w]] = heap_refcount[writer_trans_ptr[w]] - 1]
          /\ UNCHANGED <<heap_allocated, heap_aborted, running_trans_id, trans_lock, writer_trans_ptr, aborter_state>>
    \/ /\ aborter_state = "Done"
       /\ aborter_state' = "Idle"
       /\ UNCHANGED <<heap_allocated, heap_refcount, heap_aborted, running_trans_id, trans_lock, writer_state, writer_trans_ptr>>

Spec == Init /\ [][Next]_vars

=============================================================================
