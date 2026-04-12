----------------------- MODULE BtrfsTransactionFullBuggy -----------------------
(*
 * BtrfsTransactionFullBuggy.tla — Late-Join Defect in the Transaction State Machine
 *
 * This is the BUGGY variant of BtrfsTransactionFull.tla. It introduces the
 * late-join defect: a writer is allowed to join a transaction that is already
 * in COMMIT_START, COMMIT_DOING, UNBLOCKED, or SUPER_COMMITTED state.
 *
 * THE BUG
 * -------
 * In the real kernel, join_transaction() checks the transaction state before
 * incrementing the refcount. The check is:
 *
 *   if (cur_trans->state >= TRANS_STATE_COMMIT_START) {
 *       wait_event(fs_info->transaction_wait, ...);
 *       goto loop;
 *   }
 *
 * The bug is introduced by removing or weakening this check — for example,
 * if the check is accidentally placed AFTER the refcount increment, or if
 * a code path bypasses the check entirely (e.g., via a "fast path" that
 * skips the state validation for performance reasons).
 *
 * CONSEQUENCE
 * -----------
 * A writer that joins in COMMIT_START or later holds a handle to a transaction
 * that the committer is actively committing. When CommitterComplete fires, it
 * checks trans_refcount = 0 — but the late-joining writer still holds a
 * reference. This means either:
 *   (a) CommitterComplete is blocked forever (liveness violation), or
 *   (b) If CommitterComplete does not check the refcount (a second bug),
 *       the transaction object is freed while the writer still holds a handle
 *       (use-after-free / safety violation).
 *
 * This model introduces the late-join bug and also weakens CommitterComplete
 * to NOT check for active writers (simulating a second, related bug where the
 * committer assumes no writers can be active at SUPER_COMMITTED). TLC will
 * find the resulting NoUAFOnComplete / NoActiveOnCompleted violation.
 *
 * PROPERTIES VIOLATED
 * -------------------
 *   NoUAFOnComplete:    trans_state = COMPLETED but trans_refcount > 0
 *   NoActiveOnCompleted: trans_state = COMPLETED but some writer is Active
 *
 * CORRECT FIX (in BtrfsTransactionFull.tla)
 * ------------------------------------------
 *   WriterJoinSuccess only allows joining in {RUNNING, COMMIT_PREP}.
 *   CommitterComplete requires trans_refcount = 0 AND no TryJoin writers.
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    NumWriters,
    MaxOps,
    MaxWritersBeforeCommit

ASSUME NumWriters \in 1..8
ASSUME MaxOps \in 1..20
ASSUME MaxWritersBeforeCommit \in 1..NumWriters

Writers == 1..NumWriters

(* ---------------------------------------------------------------------------
 * Transaction states (identical to the correct model)
 * --------------------------------------------------------------------------- *)

TRANS_STATE_RUNNING         == "RUNNING"
TRANS_STATE_COMMIT_PREP     == "COMMIT_PREP"
TRANS_STATE_COMMIT_START    == "COMMIT_START"
TRANS_STATE_COMMIT_DOING    == "COMMIT_DOING"
TRANS_STATE_UNBLOCKED       == "UNBLOCKED"
TRANS_STATE_SUPER_COMMITTED == "SUPER_COMMITTED"
TRANS_STATE_COMPLETED       == "COMPLETED"
TRANS_STATE_ABORTED         == "ABORTED"

TerminalStates == {TRANS_STATE_COMPLETED, TRANS_STATE_ABORTED}

(* ---------------------------------------------------------------------------
 * State variables (identical to the correct model)
 * --------------------------------------------------------------------------- *)

VARIABLES
    trans_state,
    trans_refcount,
    trans_aborted,
    writer_state,
    writer_trans_ok,
    committer_state,
    aborter_state,
    ops_count,
    total_joins

vars == <<trans_state, trans_refcount, trans_aborted, writer_state,
          writer_trans_ok, committer_state, aborter_state, ops_count, total_joins>>

Init ==
    /\ trans_state     = TRANS_STATE_RUNNING
    /\ trans_refcount  = 0
    /\ trans_aborted   = FALSE
    /\ writer_state    = [w \in Writers |-> "Idle"]
    /\ writer_trans_ok = [w \in Writers |-> FALSE]
    /\ committer_state = "Idle"
    /\ aborter_state   = "Idle"
    /\ ops_count       = 0
    /\ total_joins     = 0

(* ---------------------------------------------------------------------------
 * Writer actions
 *
 * THE BUG IS HERE: WriterJoinSuccess allows joining in ANY non-terminal
 * state, including COMMIT_START, COMMIT_DOING, UNBLOCKED, SUPER_COMMITTED.
 *
 * The correct model restricts joining to {RUNNING, COMMIT_PREP} only.
 * --------------------------------------------------------------------------- *)

WriterTryJoin(w) ==
    /\ writer_state[w] = "Idle"
    /\ ops_count < MaxOps
    /\ trans_state \notin TerminalStates
    /\ writer_state' = [writer_state EXCEPT ![w] = "TryJoin"]
    /\ ops_count'    = ops_count + 1
    /\ UNCHANGED <<trans_state, trans_refcount, trans_aborted,
                   writer_trans_ok, committer_state, aborter_state, total_joins>>

\* BUG: writer can join in ANY non-terminal state, including COMMIT_START+
WriterJoinSuccess(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ trans_state \notin TerminalStates   \* BUG: missing state >= COMMIT_START check
    /\ trans_refcount'  = trans_refcount + 1
    /\ total_joins'     = total_joins + 1
    /\ writer_state'    = [writer_state    EXCEPT ![w] = "Active"]
    /\ writer_trans_ok' = [writer_trans_ok EXCEPT ![w] = TRUE]
    /\ UNCHANGED <<trans_state, trans_aborted, committer_state,
                   aborter_state, ops_count>>

\* Writers no longer block on COMMIT_START (the check is gone)
\* So WriterBlocked is only triggered for terminal states (which are handled
\* by WriterBailOut). This action is now unreachable in the buggy model.
WriterBlocked(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ trans_state \in TerminalStates   \* unreachable: BailOut handles this
    /\ writer_state' = [writer_state EXCEPT ![w] = "Blocked"]
    /\ UNCHANGED <<trans_state, trans_refcount, trans_aborted,
                   writer_trans_ok, committer_state, aborter_state, ops_count, total_joins>>

WriterWoken(w) ==
    /\ writer_state[w] = "Blocked"
    /\ trans_state \in {TRANS_STATE_UNBLOCKED, TRANS_STATE_SUPER_COMMITTED,
                        TRANS_STATE_COMPLETED, TRANS_STATE_ABORTED}
    /\ writer_state' = [writer_state EXCEPT ![w] = "Idle"]
    /\ UNCHANGED <<trans_state, trans_refcount, trans_aborted,
                   writer_trans_ok, committer_state, aborter_state, ops_count, total_joins>>

WriterDone(w) ==
    /\ writer_state[w] = "Active"
    /\ trans_refcount'  = trans_refcount - 1
    /\ writer_state'    = [writer_state EXCEPT ![w] = "Done"]
    /\ UNCHANGED <<trans_state, trans_aborted, writer_trans_ok,
                   committer_state, aborter_state, ops_count, total_joins>>

WriterBailOut(w) ==
    /\ writer_state[w] = "TryJoin"
    /\ trans_state \in TerminalStates
    /\ writer_state' = [writer_state EXCEPT ![w] = "Idle"]
    /\ UNCHANGED <<trans_state, trans_refcount, trans_aborted,
                   writer_trans_ok, committer_state, aborter_state, ops_count, total_joins>>

WriterReset(w) ==
    /\ writer_state[w] = "Done"
    /\ ops_count < MaxOps
    /\ writer_state'    = [writer_state    EXCEPT ![w] = "Idle"]
    /\ writer_trans_ok' = [writer_trans_ok EXCEPT ![w] = FALSE]
    /\ UNCHANGED <<trans_state, trans_refcount, trans_aborted,
                   committer_state, aborter_state, ops_count, total_joins>>

(* ---------------------------------------------------------------------------
 * Committer actions
 *
 * THE SECOND BUG IS HERE: CommitterComplete does NOT check for active writers
 * or TryJoin writers. It only checks trans_refcount = 0. But because the
 * late-joining writer increments the refcount, the committer will be blocked
 * until the writer releases. However, if we also remove the refcount check
 * (simulating an optimistic "no writers can be here" assumption), we get
 * an immediate UAF.
 *
 * We model BOTH variants:
 *   - With refcount check: liveness violation (committer stuck at SUPER_COMMITTED)
 *   - Without refcount check (BUGGY_COMPLETE=TRUE): safety violation (UAF)
 *
 * This model uses the WITHOUT refcount check variant to demonstrate the UAF.
 * --------------------------------------------------------------------------- *)

CommitterStart ==
    /\ committer_state = "Idle"
    /\ trans_state = TRANS_STATE_RUNNING
    /\ total_joins >= MaxWritersBeforeCommit
    /\ committer_state' = "Committing"
    /\ trans_state'     = TRANS_STATE_COMMIT_PREP
    /\ ops_count'       = ops_count + 1
    /\ UNCHANGED <<trans_refcount, trans_aborted, writer_state,
                   writer_trans_ok, aborter_state, total_joins>>

CommitterAdvance(from_state, to_state) ==
    /\ committer_state = "Committing"
    /\ trans_state = from_state
    /\ trans_state' = to_state
    /\ UNCHANGED <<trans_refcount, trans_aborted, writer_state,
                   writer_trans_ok, committer_state, aborter_state, ops_count, total_joins>>

CommitterPrepToStart    == CommitterAdvance(TRANS_STATE_COMMIT_PREP,     TRANS_STATE_COMMIT_START)
CommitterStartToDoing   == CommitterAdvance(TRANS_STATE_COMMIT_START,    TRANS_STATE_COMMIT_DOING)
CommitterDoingToUnblocked == CommitterAdvance(TRANS_STATE_COMMIT_DOING,  TRANS_STATE_UNBLOCKED)
CommitterUnblockedToSuperCommitted == CommitterAdvance(TRANS_STATE_UNBLOCKED, TRANS_STATE_SUPER_COMMITTED)

\* BUG: CommitterComplete does NOT check for active writers.
\* It assumes that by SUPER_COMMITTED, no writer can still be active.
\* This assumption is violated by the late-join bug above.
CommitterComplete ==
    /\ committer_state = "Committing"
    /\ trans_state = TRANS_STATE_SUPER_COMMITTED
    /\ ~trans_aborted
    \* BUG: missing /\ trans_refcount = 0
    \* BUG: missing /\ \A w \in Writers : writer_state[w] \notin {"Active", "TryJoin"}
    /\ trans_state'     = TRANS_STATE_COMPLETED
    /\ committer_state' = "Done"
    /\ UNCHANGED <<trans_refcount, trans_aborted, writer_state,
                   writer_trans_ok, aborter_state, ops_count, total_joins>>

(* ---------------------------------------------------------------------------
 * Aborter actions (identical to correct model)
 * --------------------------------------------------------------------------- *)

AborterAbort ==
    /\ aborter_state = "Idle"
    /\ trans_state \notin TerminalStates
    /\ trans_state'   = TRANS_STATE_ABORTED
    /\ trans_aborted' = TRUE
    /\ aborter_state' = "Done"
    /\ ops_count'     = ops_count + 1
    /\ UNCHANGED <<trans_refcount, writer_state, writer_trans_ok,
                   committer_state, total_joins>>

(* ---------------------------------------------------------------------------
 * Stutter / termination
 * --------------------------------------------------------------------------- *)

TerminalStutter ==
    /\ trans_state \in TerminalStates
    /\ \A w \in Writers : writer_state[w] \in {"Idle", "Done", "Blocked"}
    /\ UNCHANGED vars

Stutter ==
    /\ ops_count >= MaxOps
    /\ UNCHANGED vars

(* ---------------------------------------------------------------------------
 * Next-state relation and fairness
 * --------------------------------------------------------------------------- *)

Next ==
    \/ CommitterStart
    \/ CommitterPrepToStart
    \/ CommitterStartToDoing
    \/ CommitterDoingToUnblocked
    \/ CommitterUnblockedToSuperCommitted
    \/ CommitterComplete
    \/ AborterAbort
    \/ \E w \in Writers :
           WriterTryJoin(w) \/ WriterJoinSuccess(w) \/ WriterBlocked(w) \/
           WriterWoken(w) \/ WriterDone(w) \/ WriterReset(w) \/ WriterBailOut(w)
    \/ TerminalStutter
    \/ Stutter

Fairness ==
    /\ SF_vars(CommitterStart)
    /\ WF_vars(CommitterPrepToStart)
    /\ WF_vars(CommitterStartToDoing)
    /\ WF_vars(CommitterDoingToUnblocked)
    /\ WF_vars(CommitterUnblockedToSuperCommitted)
    /\ WF_vars(CommitterComplete)
    /\ \A w \in Writers :
           /\ WF_vars(WriterTryJoin(w))
           /\ WF_vars(WriterJoinSuccess(w))
           /\ WF_vars(WriterBlocked(w))
           /\ SF_vars(WriterWoken(w))
           /\ WF_vars(WriterDone(w))
           /\ WF_vars(WriterReset(w))
           /\ WF_vars(WriterBailOut(w))

Spec == Init /\ [][Next]_vars /\ Fairness

(* ---------------------------------------------------------------------------
 * Safety invariants
 * --------------------------------------------------------------------------- *)

\* VIOLATED BY THIS MODEL: transaction freed while writer holds a handle
NoUAFOnComplete ==
    trans_state = TRANS_STATE_COMPLETED => trans_refcount = 0

\* VIOLATED BY THIS MODEL: writer is Active when transaction is COMPLETED
NoActiveOnCompleted ==
    trans_state = TRANS_STATE_COMPLETED =>
        \A w \in Writers : writer_state[w] \notin {"Active", "TryJoin"}

\* Refcount must never go negative
RefcountNonNegative ==
    trans_refcount >= 0

\* No writer should hold a handle to an aborted transaction
NoHandleOnAborted ==
    trans_aborted =>
        \A w \in Writers : writer_state[w] \notin {"Active"}

(* ---------------------------------------------------------------------------
 * Liveness properties
 * --------------------------------------------------------------------------- *)

BlockedWriterEventuallyWoken ==
    \A w \in Writers :
        [](writer_state[w] = "Blocked" =>
           <>(writer_state[w] \in {"Idle", "Done"}))

EventuallyTerminal ==
    <>(trans_state \in TerminalStates)

=============================================================================
