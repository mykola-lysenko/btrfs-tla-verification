------------------------ MODULE BtrfsTransactionAbort ------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

(*
 * BtrfsTransactionAbort.tla — Full Transaction Abort State Machine
 *
 * This model captures the complete transaction lifecycle in btrfs, including:
 *
 *   1. COMMIT STATE MACHINE
 *      RUNNING -> COMMIT_START -> COMMIT_DOING -> UNBLOCKED
 *               -> SUPER_COMMITTED -> COMPLETED
 *      At any point, an error can trigger the abort path.
 *
 *   2. ABORT PATH (cleanup_transaction)
 *      - Sets BTRFS_FS_STATE_ERROR on fs_info
 *      - Marks trans->aborted
 *      - Walks the trans_list to wake all blocked writers
 *      - Removes the transaction from the running list
 *      - Decrements the refcount (triggers free when it reaches 0)
 *
 *   3. WRITER THREADS (NumWriters)
 *      Each writer can:
 *      - Join the transaction (bumps refcount while holding trans_lock)
 *      - Block waiting for the transaction to reach UNBLOCKED
 *      - Be woken by the abort path
 *      - Leave the transaction (decrements refcount)
 *
 *   4. TRANS_LIST WALK
 *      The abort path walks all writers in trans_list and wakes them.
 *      This is the critical path that must wake ALL blocked writers.
 *
 * KEY PROPERTIES
 * --------------
 *   AbortSafety:    If trans_state = ABORTED then fs_error = TRUE
 *   NoUAF:          No writer accesses a freed transaction object
 *   WaiterNeverStuck: Every blocked writer is eventually woken
 *   NoNewTransAfterAbort: No new transaction starts after fs_error = TRUE
 *   RefcountSafety: heap_refcount never goes negative
 *)

CONSTANTS
    NumWriters,       \* e.g., 3
    MaxTransactions   \* e.g., 2 (heap slots)

ASSUME NumWriters \in Nat /\ NumWriters >= 1
ASSUME MaxTransactions \in Nat /\ MaxTransactions >= 1

WS == 1..NumWriters
TS == 1..MaxTransactions

\* Transaction commit states
TransStates == {"NONE", "RUNNING", "COMMIT_START", "COMMIT_DOING",
                "UNBLOCKED", "SUPER_COMMITTED", "COMPLETED", "ABORTED"}

\* Writer states
WriterStates == {"Idle", "Joining", "Joined", "Blocking", "Blocked",
                 "Woken", "Leaving", "Done", "Error"}

VARIABLES
    \* Filesystem-level state
    fs_error,         \* BOOLEAN: BTRFS_FS_STATE_ERROR

    \* Transaction heap
    heap_alloc,       \* [TS -> BOOLEAN]
    heap_refcount,    \* [TS -> Nat]
    heap_aborted,     \* [TS -> BOOLEAN]
    heap_state,       \* [TS -> TransStates]

    \* Running transaction pointer (0 = none)
    running_trans,    \* 0..MaxTransactions

    \* trans_lock protecting running_trans and join path
    trans_lock,       \* BOOLEAN

    \* Writer state
    w_state,          \* [WS -> WriterStates]
    w_trans,          \* [WS -> 0..MaxTransactions] (which trans the writer joined)

    \* Aborter state
    aborter_state,    \* "Idle" | "MarkError" | "WalkList" | "RemoveTrans" | "Done"
    aborter_target,   \* 0..MaxTransactions
    aborter_walk_idx  \* 0..NumWriters (index into trans_list walk)

vars == <<fs_error, heap_alloc, heap_refcount, heap_aborted, heap_state,
          running_trans, trans_lock, w_state, w_trans,
          aborter_state, aborter_target, aborter_walk_idx>>

-----------------------------------------------------------------------------
\* HELPERS

LiveTrans == {t \in TS : heap_alloc[t] = TRUE}
BlockedWriters(t) == {w \in WS : w_state[w] = "Blocked" /\ w_trans[w] = t}

-----------------------------------------------------------------------------
\* INIT

Init ==
    /\ fs_error = FALSE
    /\ heap_alloc    = [t \in TS |-> FALSE]
    /\ heap_refcount = [t \in TS |-> 0]
    /\ heap_aborted  = [t \in TS |-> FALSE]
    /\ heap_state    = [t \in TS |-> "NONE"]
    /\ running_trans = 0
    /\ trans_lock = FALSE
    /\ w_state = [w \in WS |-> "Idle"]
    /\ w_trans = [w \in WS |-> 0]
    /\ aborter_state = "Idle"
    /\ aborter_target = 0
    /\ aborter_walk_idx = 0

-----------------------------------------------------------------------------
\* BACKGROUND: create and free transactions

CreateTrans ==
    /\ running_trans = 0
    /\ fs_error = FALSE
    /\ trans_lock = FALSE
    /\ \E t \in TS : heap_alloc[t] = FALSE
    /\ LET t == CHOOSE t \in TS : heap_alloc[t] = FALSE IN
       /\ heap_alloc'    = [heap_alloc    EXCEPT ![t] = TRUE]
       /\ heap_refcount' = [heap_refcount EXCEPT ![t] = 1]
       /\ heap_aborted'  = [heap_aborted  EXCEPT ![t] = FALSE]
       /\ heap_state'    = [heap_state    EXCEPT ![t] = "RUNNING"]
       /\ running_trans' = t
    /\ UNCHANGED <<fs_error, trans_lock, w_state, w_trans,
                   aborter_state, aborter_target, aborter_walk_idx>>

FreeTrans ==
    /\ \E t \in TS : heap_alloc[t] = TRUE /\ heap_refcount[t] = 0
    /\ LET t == CHOOSE t \in TS : heap_alloc[t] = TRUE /\ heap_refcount[t] = 0 IN
       /\ heap_alloc' = [heap_alloc EXCEPT ![t] = FALSE]
       /\ heap_state' = [heap_state EXCEPT ![t] = "NONE"]
    /\ UNCHANGED <<fs_error, heap_refcount, heap_aborted, running_trans, trans_lock,
                   w_state, w_trans, aborter_state, aborter_target, aborter_walk_idx>>

-----------------------------------------------------------------------------
\* COMMIT PATH

CommitAdvance ==
    /\ running_trans /= 0
    /\ fs_error = FALSE
    /\ aborter_state = "Idle"
    /\ trans_lock = FALSE   \* commit only advances when lock is free
    /\ LET t == running_trans
           s == heap_state[t]
       IN
       /\ s \in {"RUNNING","COMMIT_START","COMMIT_DOING","UNBLOCKED","SUPER_COMMITTED"}
       /\ heap_state' = [heap_state EXCEPT ![t] =
            CASE s = "RUNNING"          -> "COMMIT_START"
              [] s = "COMMIT_START"     -> "COMMIT_DOING"
              [] s = "COMMIT_DOING"     -> "UNBLOCKED"
              [] s = "UNBLOCKED"        -> "SUPER_COMMITTED"
              [] s = "SUPER_COMMITTED"  -> "COMPLETED"
              [] OTHER                  -> s]
    /\ UNCHANGED <<fs_error, heap_alloc, heap_refcount, heap_aborted, running_trans,
                   trans_lock, w_state, w_trans,
                   aborter_state, aborter_target, aborter_walk_idx>>

CommitComplete ==
    /\ running_trans /= 0
    /\ heap_state[running_trans] = "COMPLETED"
    /\ heap_refcount' = [heap_refcount EXCEPT ![running_trans] = heap_refcount[running_trans] - 1]
    /\ running_trans' = 0
    /\ UNCHANGED <<fs_error, heap_alloc, heap_aborted, heap_state, trans_lock,
                   w_state, w_trans, aborter_state, aborter_target, aborter_walk_idx>>

-----------------------------------------------------------------------------
\* WRITER PATH

\* Step 1: acquire trans_lock, read running_trans, bump refcount
WriterJoin(w) ==
    /\ w_state[w] = "Idle"
    /\ trans_lock = FALSE
    /\ running_trans /= 0
    /\ fs_error = FALSE
    /\ LET t == running_trans IN
       /\ heap_state[t] \in {"RUNNING","COMMIT_START"}
       /\ trans_lock' = TRUE
       /\ heap_refcount' = [heap_refcount EXCEPT ![t] = heap_refcount[t] + 1]
       /\ w_trans' = [w_trans EXCEPT ![w] = t]
       /\ w_state' = [w_state EXCEPT ![w] = "Joining"]
    /\ UNCHANGED <<fs_error, heap_alloc, heap_aborted, heap_state, running_trans,
                   aborter_state, aborter_target, aborter_walk_idx>>

\* Step 2: release trans_lock
WriterDropLock(w) ==
    /\ w_state[w] = "Joining"
    /\ trans_lock' = FALSE
    /\ w_state' = [w_state EXCEPT ![w] = "Joined"]
    /\ UNCHANGED <<fs_error, heap_alloc, heap_refcount, heap_aborted, heap_state,
                   running_trans, w_trans, aborter_state, aborter_target, aborter_walk_idx>>

\* Step 3a: writer decides to block waiting for UNBLOCKED
WriterBlock(w) ==
    /\ w_state[w] = "Joined"
    /\ w_trans[w] /= 0
    /\ heap_state[w_trans[w]] \in {"COMMIT_START","COMMIT_DOING"}
    /\ w_state' = [w_state EXCEPT ![w] = "Blocked"]
    /\ UNCHANGED <<fs_error, heap_alloc, heap_refcount, heap_aborted, heap_state,
                   running_trans, trans_lock, w_trans,
                   aborter_state, aborter_target, aborter_walk_idx>>

\* Step 3b: writer proceeds without blocking (transaction already unblocked)
WriterProceed(w) ==
    /\ w_state[w] = "Joined"
    /\ w_trans[w] /= 0
    /\ heap_state[w_trans[w]] \in {"UNBLOCKED","SUPER_COMMITTED","COMPLETED","ABORTED"}
    /\ w_state' = [w_state EXCEPT ![w] = IF heap_aborted[w_trans[w]] THEN "Error" ELSE "Done"]
    /\ UNCHANGED <<fs_error, heap_alloc, heap_refcount, heap_aborted, heap_state,
                   running_trans, trans_lock, w_trans,
                   aborter_state, aborter_target, aborter_walk_idx>>

\* Step 4: woken writer checks abort status
WriterWoken(w) ==
    /\ w_state[w] = "Woken"
    /\ w_trans[w] /= 0
    /\ Assert(heap_alloc[w_trans[w]], "UAF: woken writer accessed freed transaction!")
    /\ w_state' = [w_state EXCEPT ![w] = IF heap_aborted[w_trans[w]] THEN "Error" ELSE "Done"]
    /\ UNCHANGED <<fs_error, heap_alloc, heap_refcount, heap_aborted, heap_state,
                   running_trans, trans_lock, w_trans,
                   aborter_state, aborter_target, aborter_walk_idx>>

\* Step 5: writer leaves, drops refcount
WriterLeave(w) ==
    /\ w_state[w] \in {"Done","Error"}
    /\ w_trans[w] /= 0
    /\ heap_refcount' = [heap_refcount EXCEPT ![w_trans[w]] = heap_refcount[w_trans[w]] - 1]
    /\ w_state' = [w_state EXCEPT ![w] = "Idle"]
    /\ w_trans' = [w_trans EXCEPT ![w] = 0]
    /\ UNCHANGED <<fs_error, heap_alloc, heap_aborted, heap_state, running_trans,
                   trans_lock, aborter_state, aborter_target, aborter_walk_idx>>

-----------------------------------------------------------------------------
\* ABORT PATH (models cleanup_transaction)

\* Step 1: aborter fires — marks fs_error and trans->aborted
AbortStep1 ==
    /\ aborter_state = "Idle"
    /\ running_trans /= 0
    /\ trans_lock = FALSE
    /\ LET t == running_trans IN
       /\ heap_state[t] \in {"RUNNING","COMMIT_START","COMMIT_DOING","UNBLOCKED"}
       /\ fs_error' = TRUE
       /\ heap_aborted' = [heap_aborted EXCEPT ![t] = TRUE]
       /\ heap_state' = [heap_state EXCEPT ![t] = "ABORTED"]
       /\ aborter_target' = t
       /\ aborter_walk_idx' = 1
       /\ aborter_state' = "WalkList"
    /\ UNCHANGED <<heap_alloc, heap_refcount, running_trans, trans_lock,
                   w_state, w_trans>>

\* Step 2: walk trans_list — wake each blocked writer one by one
AbortWalkList ==
    /\ aborter_state = "WalkList"
    /\ aborter_walk_idx <= NumWriters
    /\ LET w == aborter_walk_idx IN
       /\ IF w_state[w] = "Blocked" /\ w_trans[w] = aborter_target THEN
              w_state' = [w_state EXCEPT ![w] = "Woken"]
          ELSE
              UNCHANGED <<w_state>>
       /\ aborter_walk_idx' = aborter_walk_idx + 1
    /\ UNCHANGED <<fs_error, heap_alloc, heap_refcount, heap_aborted, heap_state,
                   running_trans, trans_lock, w_trans,
                   aborter_state, aborter_target>>

\* Step 3: walk complete — remove transaction from running list, drop refcount
AbortRemoveTrans ==
    /\ aborter_state = "WalkList"
    /\ aborter_walk_idx > NumWriters
    /\ LET t == aborter_target IN
       /\ heap_refcount' = [heap_refcount EXCEPT ![t] = heap_refcount[t] - 1]
       /\ running_trans' = 0
    /\ aborter_state' = "Done"
    /\ UNCHANGED <<fs_error, heap_alloc, heap_aborted, heap_state, trans_lock,
                   w_state, w_trans, aborter_target, aborter_walk_idx>>

AbortReset ==
    /\ aborter_state = "Done"
    /\ aborter_state' = "Idle"
    /\ aborter_target' = 0
    /\ aborter_walk_idx' = 0
    /\ UNCHANGED <<fs_error, heap_alloc, heap_refcount, heap_aborted, heap_state,
                   running_trans, trans_lock, w_state, w_trans>>

-----------------------------------------------------------------------------
\* NEXT STA

-----------------------------------------------------------------------------
\* COMMIT WAKEUP: when transaction reaches UNBLOCKED, wake all blocked writers

\* CommitWakeup(w): wake a specific blocked writer w whose transaction is done
CommitWakeup(w) ==
    /\ w_state[w] = "Blocked"
    /\ w_trans[w] /= 0
    /\ heap_state[w_trans[w]] \in {"UNBLOCKED","SUPER_COMMITTED","COMPLETED","ABORTED"}
    /\ w_state' = [ww \in WS |-> IF ww = w THEN "Woken" ELSE w_state[ww]]
    /\ UNCHANGED <<fs_error, heap_alloc, heap_refcount, heap_aborted, heap_state,
                   running_trans, trans_lock, w_trans,
                   aborter_state, aborter_target, aborter_walk_idx>>


Next ==
    \/ CreateTrans
    \/ FreeTrans
    \/ CommitAdvance
    \/ CommitComplete
    \/ \E w \in WS :
          WriterJoin(w) \/ WriterDropLock(w) \/ WriterBlock(w) \/
          WriterProceed(w) \/ WriterWoken(w) \/ WriterLeave(w)
    \/ AbortStep1
    \/ AbortWalkList
    \/ AbortRemoveTrans
    \/ AbortReset
    \/ \E w \in WS : CommitWakeup(w)
    \* Terminal stutter: fs in error state, all writers idle, no running trans
    \/ /\ fs_error = TRUE
       /\ running_trans = 0
       /\ aborter_state = "Idle"
       /\ \A w \in WS : w_state[w] = "Idle"
       /\ UNCHANGED vars

Fairness ==
    /\ WF_vars(CreateTrans)
    /\ WF_vars(CommitAdvance)
    /\ \A w \in WS : SF_vars(CommitWakeup(w))
    /\ WF_vars(CommitComplete)
    /\ WF_vars(AbortStep1)
    /\ WF_vars(AbortWalkList)
    /\ WF_vars(AbortRemoveTrans)
    /\ WF_vars(AbortReset)
    /\ \A w \in WS :
          /\ WF_vars(WriterJoin(w))
          /\ WF_vars(WriterDropLock(w))
          /\ WF_vars(WriterWoken(w))
          /\ WF_vars(WriterLeave(w))
          /\ WF_vars(WriterProceed(w))
          /\ WF_vars(WriterBlock(w))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* PROPERTIES

\* Safety: abort always sets fs_error
AbortSafety ==
    \A t \in TS : heap_state[t] = "ABORTED" => fs_error = TRUE

\* Safety: refcount never goes negative
RefcountSafety ==
    \A t \in TS : heap_refcount[t] >= 0

\* Safety: no new transaction starts after fs_error
NoNewTransAfterAbort ==
    fs_error => (running_trans = 0 \/ heap_state[running_trans] = "ABORTED")

\* Safety: no writer accesses a freed transaction
NoUAF ==
    \A w \in WS : w_trans[w] /= 0 => heap_alloc[w_trans[w]] = TRUE

\* Liveness: every blocked writer is eventually woken or done
WaiterNeverStuck ==
    \A w \in WS : (w_state[w] = "Blocked") ~> (w_state[w] \in {"Woken","Done","Error","Idle"})

\* Liveness: the system always makes progress (transaction eventually terminates)
TransEventuallyTerminates ==
    \A t \in TS : (heap_state[t] = "RUNNING") ~> (heap_state[t] \in {"COMPLETED","ABORTED","NONE"})

=============================================================================
