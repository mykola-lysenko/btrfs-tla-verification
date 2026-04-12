------------------------ MODULE BtrfsTransactionUAFNFixed ------------------------
EXTENDS Integers, FiniteSets, TLC

(*
 * BtrfsTransactionUAFNFixed.tla — CVE-2025-21753 (Transaction UAF)
 *
 * FIXED variant: writers bump the refcount WHILE holding the trans_lock,
 * before dropping it. This ensures the transaction object cannot be freed
 * while the writer still holds a reference.
 *)

CONSTANTS
    NumWriters,
    NumAborters,
    MaxTransactions

ASSUME NumWriters \in Nat /\ NumWriters >= 1
ASSUME NumAborters \in Nat /\ NumAborters >= 1
ASSUME MaxTransactions \in Nat /\ MaxTransactions >= 1

VARIABLES
    heap_alloc,
    heap_refcount,
    heap_aborted,
    running_trans,
    trans_lock,
    w_pc,
    w_ptr,
    ab_pc,
    ab_target

vars == <<heap_alloc, heap_refcount, heap_aborted, running_trans, trans_lock,
          w_pc, w_ptr, ab_pc, ab_target>>

WS == 1..NumWriters
AS == 1..NumAborters
TS == 1..MaxTransactions

Init ==
    /\ heap_alloc    = [t \in TS |-> FALSE]
    /\ heap_refcount = [t \in TS |-> 0]
    /\ heap_aborted  = [t \in TS |-> FALSE]
    /\ running_trans = 0
    /\ trans_lock = FALSE
    /\ w_pc  = [w \in WS |-> "Idle"]
    /\ w_ptr = [w \in WS |-> 0]
    /\ ab_pc = [a \in AS |-> "Idle"]
    /\ ab_target = [a \in AS |-> 0]

CreateTrans ==
    /\ running_trans = 0
    /\ trans_lock = FALSE
    /\ \E t \in TS : heap_alloc[t] = FALSE
    /\ LET t == CHOOSE t \in TS : heap_alloc[t] = FALSE IN
       /\ heap_alloc'    = [heap_alloc    EXCEPT ![t] = TRUE]
       /\ heap_refcount' = [heap_refcount EXCEPT ![t] = 1]
       /\ heap_aborted'  = [heap_aborted  EXCEPT ![t] = FALSE]
       /\ running_trans' = t
    /\ UNCHANGED <<trans_lock, w_pc, w_ptr, ab_pc, ab_target>>

FreeTrans ==
    /\ \E t \in TS : heap_alloc[t] = TRUE /\ heap_refcount[t] = 0
    /\ LET t == CHOOSE t \in TS : heap_alloc[t] = TRUE /\ heap_refcount[t] = 0 IN
       heap_alloc' = [heap_alloc EXCEPT ![t] = FALSE]
    /\ UNCHANGED <<heap_refcount, heap_aborted, running_trans, trans_lock, w_pc, w_ptr, ab_pc, ab_target>>

\* ---- Writer (FIXED: bumps refcount while holding lock) ----

WLock(w) ==
    /\ w_pc[w] = "Idle"
    /\ trans_lock = FALSE
    /\ running_trans /= 0
    /\ trans_lock' = TRUE
    /\ w_ptr' = [w_ptr EXCEPT ![w] = running_trans]
    \* FIX: bump refcount BEFORE dropping the lock
    /\ heap_refcount' = [heap_refcount EXCEPT ![running_trans] = heap_refcount[running_trans] + 1]
    /\ w_pc'  = [w_pc  EXCEPT ![w] = "DropLock"]
    /\ UNCHANGED <<heap_alloc, heap_aborted, running_trans, ab_pc, ab_target>>

WDropLock(w) ==
    /\ w_pc[w] = "DropLock"
    /\ trans_lock' = FALSE
    /\ w_pc' = [w_pc EXCEPT ![w] = "ReadAborted"]
    /\ UNCHANGED <<heap_alloc, heap_refcount, heap_aborted, running_trans, w_ptr, ab_pc, ab_target>>

WReadAborted(w) ==
    /\ w_pc[w] = "ReadAborted"
    /\ w_ptr[w] /= 0
    \* Because we hold a refcount, the object MUST still be allocated
    /\ Assert(heap_alloc[w_ptr[w]],
              "UAF: writer accessed freed transaction object!")
    /\ w_pc' = [w_pc EXCEPT ![w] = IF heap_aborted[w_ptr[w]] THEN "Error" ELSE "Done"]
    /\ UNCHANGED <<heap_alloc, heap_refcount, heap_aborted, running_trans, trans_lock, w_ptr, ab_pc, ab_target>>

WRelease(w) ==
    /\ w_pc[w] \in {"Done","Error"}
    /\ w_ptr[w] /= 0
    /\ heap_refcount' = [heap_refcount EXCEPT ![w_ptr[w]] = heap_refcount[w_ptr[w]] - 1]
    /\ w_pc'  = [w_pc  EXCEPT ![w] = "Idle"]
    /\ w_ptr' = [w_ptr EXCEPT ![w] = 0]
    /\ UNCHANGED <<heap_alloc, heap_aborted, running_trans, trans_lock, ab_pc, ab_target>>

\* ---- Aborter ----

AbLock(a) ==
    /\ ab_pc[a] = "Idle"
    /\ trans_lock = FALSE
    /\ running_trans /= 0
    /\ trans_lock' = TRUE
    /\ ab_target' = [ab_target EXCEPT ![a] = running_trans]
    /\ ab_pc' = [ab_pc EXCEPT ![a] = "MarkAborted"]
    /\ UNCHANGED <<heap_alloc, heap_refcount, heap_aborted, running_trans, w_pc, w_ptr>>

AbMark(a) ==
    /\ ab_pc[a] = "MarkAborted"
    /\ LET t == ab_target[a] IN
       /\ heap_aborted' = [heap_aborted EXCEPT ![t] = TRUE]
       /\ heap_refcount' = [heap_refcount EXCEPT ![t] = heap_refcount[t] - 1]
       /\ running_trans' = 0
    /\ trans_lock' = FALSE
    /\ ab_pc' = [ab_pc EXCEPT ![a] = "Done"]
    /\ UNCHANGED <<heap_alloc, w_pc, w_ptr, ab_target>>

AbReset(a) ==
    /\ ab_pc[a] = "Done"
    /\ ab_pc' = [ab_pc EXCEPT ![a] = "Idle"]
    /\ ab_target' = [ab_target EXCEPT ![a] = 0]
    /\ UNCHANGED <<heap_alloc, heap_refcount, heap_aborted, running_trans, trans_lock, w_pc, w_ptr>>

Next ==
    \/ CreateTrans
    \/ FreeTrans
    \/ \E w \in WS : WLock(w) \/ WDropLock(w) \/ WReadAborted(w) \/ WRelease(w)
    \/ \E a \in AS : AbLock(a) \/ AbMark(a) \/ AbReset(a)

Spec == Init /\ [][Next]_vars

=============================================================================
