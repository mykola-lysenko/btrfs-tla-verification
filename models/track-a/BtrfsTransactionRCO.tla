------------------------ MODULE BtrfsTransactionRCO ------------------------
EXTENDS Integers, FiniteSets, TLC

(*
 * BtrfsTransactionRCO.tla — Transaction UAF using RefcountedObject module
 *
 * This spec validates the RefcountedObject module by re-implementing the
 * transaction join/abort UAF (CVE-2025-21753) using the generic module.
 *
 * A writer calls join_transaction():
 *   1. Acquire trans_lock
 *   2. Read running_trans pointer
 *   3. Release trans_lock
 *   4. Read trans->aborted  ← UAF if aborter freed trans between 3 and 4
 *
 * The fix: call RCO_Get(trans) before step 3, RCO_Put(trans) after step 4.
 *)

CONSTANTS
    NumWriters,
    MaxTransactions

ASSUME NumWriters >= 1
ASSUME MaxTransactions >= 1

WS == 1..NumWriters
TS == 1..MaxTransactions

VARIABLES
    \* RefcountedObject state
    trans_refcount,     \* [TS -> Nat]
    trans_live,         \* [TS -> BOOLEAN]

    \* Transaction state
    trans_aborted,      \* [TS -> BOOLEAN]
    trans_state,        \* [TS -> "None"|"Running"|"Committing"|"Aborted"|"Committed"]

    \* System state
    running_trans,      \* 0..MaxTransactions (0 = none)
    trans_lock,         \* BOOLEAN (TRUE = held)
    trans_lock_holder,  \* 0..NumWriters (0 = no holder)

    \* Writer state
    writer_state,       \* [WS -> "Idle"|"AcquireLock"|"HavePtr"|"ReadAborted"|"Done"]
    writer_trans,       \* [WS -> 0..MaxTransactions]

    \* Aborter state
    aborter_state,      \* "Idle"|"Aborting"|"Done"
    aborter_trans,      \* 0..MaxTransactions

    \* Op counter
    ops_count

vars == <<trans_refcount, trans_live, trans_aborted, trans_state,
          running_trans, trans_lock, trans_lock_holder,
          writer_state, writer_trans,
          aborter_state, aborter_trans,
          ops_count>>

\* Instantiate the RefcountedObject module
RCO == INSTANCE RefcountedObject WITH
    Objects  <- TS,
    refcount <- trans_refcount,
    live     <- trans_live

-----------------------------------------------------------------------------
Init ==
    /\ trans_refcount    = [t \in TS |-> 0]
    /\ trans_live        = [t \in TS |-> FALSE]
    /\ trans_aborted     = [t \in TS |-> FALSE]
    /\ trans_state       = [t \in TS |-> "None"]
    /\ running_trans     = 0
    /\ trans_lock        = FALSE
    /\ trans_lock_holder = 0
    /\ writer_state      = [w \in WS |-> "Idle"]
    /\ writer_trans      = [w \in WS |-> 0]
    /\ aborter_state     = "Idle"
    /\ aborter_trans     = 0
    /\ ops_count         = 0

-----------------------------------------------------------------------------
\* TRANSACTION LIFECYCLE

CreateTransaction ==
    /\ running_trans = 0
    /\ ops_count < MaxTransactions
    /\ \E t \in TS : ~trans_live[t] /\ trans_refcount[t] = 0
    /\ LET t == CHOOSE t \in TS : ~trans_live[t] /\ trans_refcount[t] = 0 IN
       /\ trans_refcount' = [trans_refcount EXCEPT ![t] = 1]
       /\ trans_live'     = [trans_live     EXCEPT ![t] = TRUE]
       /\ trans_state'    = [trans_state    EXCEPT ![t] = "Running"]
       /\ trans_aborted'  = [trans_aborted  EXCEPT ![t] = FALSE]
       /\ running_trans'  = t
       /\ ops_count'      = ops_count + 1
    /\ UNCHANGED <<trans_lock, trans_lock_holder,
                   writer_state, writer_trans,
                   aborter_state, aborter_trans>>

-----------------------------------------------------------------------------
\* WRITER: join_transaction() — BUGGY version (no refcount bump)

WriterAcquireLock(w) ==
    /\ writer_state[w] = "Idle"
    /\ running_trans /= 0
    /\ ~trans_lock
    /\ trans_lock'        = TRUE
    /\ trans_lock_holder' = w
    /\ writer_state'      = [writer_state EXCEPT ![w] = "AcquireLock"]
    /\ UNCHANGED <<trans_refcount, trans_live, trans_aborted, trans_state,
                   running_trans, writer_trans,
                   aborter_state, aborter_trans, ops_count>>

WriterReadPtr(w) ==
    \* Read running_trans pointer and release lock (BUGGY: no RCO_Get)
    /\ writer_state[w] = "AcquireLock"
    /\ trans_lock_holder = w
    /\ running_trans /= 0
    /\ writer_trans'      = [writer_trans EXCEPT ![w] = running_trans]
    /\ trans_lock'        = FALSE
    /\ trans_lock_holder' = 0
    /\ writer_state'      = [writer_state EXCEPT ![w] = "HavePtr"]
    \* BUG: no RCO_Get here
    /\ UNCHANGED <<trans_refcount, trans_live, trans_aborted, trans_state,
                   running_trans, aborter_state, aborter_trans, ops_count>>

WriterReadAborted(w) ==
    \* Read trans->aborted — UAF if aborter freed trans between HavePtr and here
    /\ writer_state[w] = "HavePtr"
    /\ LET t == writer_trans[w] IN
       /\ Assert(trans_live[t],
                 <<"UAF: writer read aborted field of freed transaction", w, t>>)
       /\ writer_state' = [writer_state EXCEPT ![w] = "Done"]
    /\ UNCHANGED <<trans_refcount, trans_live, trans_aborted, trans_state,
                   running_trans, trans_lock, trans_lock_holder,
                   writer_trans, aborter_state, aborter_trans, ops_count>>

WriterReset(w) ==
    /\ writer_state[w] = "Done"
    /\ writer_state' = [writer_state EXCEPT ![w] = "Idle"]
    /\ writer_trans' = [writer_trans EXCEPT ![w] = 0]
    /\ UNCHANGED <<trans_refcount, trans_live, trans_aborted, trans_state,
                   running_trans, trans_lock, trans_lock_holder,
                   aborter_state, aborter_trans, ops_count>>

-----------------------------------------------------------------------------
\* ABORTER: cleanup_transaction()

AborterStart ==
    /\ aborter_state = "Idle"
    /\ running_trans /= 0
    /\ aborter_state' = "Aborting"
    /\ aborter_trans' = running_trans
    /\ UNCHANGED <<trans_refcount, trans_live, trans_aborted, trans_state,
                   running_trans, trans_lock, trans_lock_holder,
                   writer_state, writer_trans, ops_count>>

AborterAbort ==
    /\ aborter_state = "Aborting"
    /\ aborter_trans /= 0
    /\ LET t == aborter_trans IN
       /\ trans_live[t]
       /\ trans_state'    = [trans_state   EXCEPT ![t] = "Aborted"]
       /\ trans_aborted'  = [trans_aborted EXCEPT ![t] = TRUE]
       \* Drop the transaction's own reference (the "running_trans" reference)
       /\ IF trans_refcount[t] = 1 THEN
              /\ trans_refcount' = [trans_refcount EXCEPT ![t] = 0]
              /\ trans_live'     = [trans_live     EXCEPT ![t] = FALSE]
          ELSE
              /\ trans_refcount' = [trans_refcount EXCEPT ![t] = trans_refcount[t] - 1]
              /\ UNCHANGED trans_live
       /\ running_trans'  = 0
       /\ aborter_state'  = "Done"
    /\ UNCHANGED <<trans_lock, trans_lock_holder,
                   writer_state, writer_trans, aborter_trans, ops_count>>

AborterReset ==
    /\ aborter_state = "Done"
    /\ aborter_state' = "Idle"
    /\ aborter_trans' = 0
    /\ UNCHANGED <<trans_refcount, trans_live, trans_aborted, trans_state,
                   running_trans, trans_lock, trans_lock_holder,
                   writer_state, writer_trans, ops_count>>

-----------------------------------------------------------------------------
Terminal ==
    /\ running_trans = 0
    /\ aborter_state = "Idle"
    /\ \A w \in WS : writer_state[w] = "Idle"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
Next ==
    \/ CreateTransaction
    \/ \E w \in WS : WriterAcquireLock(w) \/ WriterReadPtr(w)
                  \/ WriterReadAborted(w) \/ WriterReset(w)
    \/ AborterStart \/ AborterAbort \/ AborterReset
    \/ Terminal

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* INVARIANTS

\* Delegate to RefcountedObject invariants
RCO_NoNegativeRefcount  == RCO!RCO_NoNegativeRefcount
RCO_LiveImpliesPositive == RCO!RCO_LiveImpliesPositive
RCO_FreeImpliesZero     == RCO!RCO_FreeImpliesZero

\* No writer should hold a raw pointer to a freed transaction
NoUAF ==
    \A w \in WS :
        writer_state[w] = "HavePtr" =>
            (writer_trans[w] /= 0 /\ trans_live[writer_trans[w]])

=============================================================================
