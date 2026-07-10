--------------------------- MODULE BtrfsQgroupTrace ---------------------------
(***************************************************************************)
(* Trace-validation spec: checks that a real kernel trace (converted by    *)
(* tracing/trace_to_tla.py into BtrfsQgroupTraceData.tla) is an accepted   *)
(* behavior of BtrfsQgroupLifecycle.                                       *)
(*                                                                         *)
(* Each step either (a) matches the next observable trace event and       *)
(* advances idx, or (b) performs an internal (unobserved) model action.    *)
(* Consuming the whole trace violates the pseudo-invariant TraceNotDone —  *)
(* so with TLC:                                                            *)
(*                                                                         *)
(*   "Invariant TraceNotDone is violated"  => TRACE ACCEPTED (success!)    *)
(*   "Deadlock reached"                    => DIVERGENCE at Trace[idx]:    *)
(*        the model cannot explain the next event; the deadlock state      *)
(*        shows how far validation got and what the model state was.       *)
(*                                                                         *)
(* Run via validate-trace.sh, which interprets the TLC output.             *)
(***************************************************************************)
EXTENDS BtrfsQgroupLifecycle, BtrfsQgroupTraceData, Naturals, Sequences

VARIABLE idx
tvars == <<vars, idx>>

TInit == Init /\ idx = 1

(***************************************************************************)
(* To tame the state-space explosion of trace validation, internal        *)
(* (unobserved) steps are attributed only to the task that owns the NEXT   *)
(* observable event. Each task walks its own pc deterministically to its   *)
(* next event; cross-task interactions are mediated entirely through the   *)
(* trace's total order (which reflects the real ts ordering). This makes   *)
(* replay near-deterministic instead of exploring all interleavings of     *)
(* independent internal actions.                                           *)
(*                                                                         *)
(* Soundness of the restriction: if event idx (owned by task A) genuinely  *)
(* required another task B to make an internal transition first, then B's  *)
(* corresponding observable event necessarily precedes idx in the trace    *)
(* (B could not have returned to the kernel otherwise), so B already ran   *)
(* its internal steps during B's turn. If that is ever false, TLC          *)
(* deadlocks and the divergence is itself a finding.                       *)
(***************************************************************************)
NextTask == IF idx <= Len(Trace) THEN Trace[idx].task ELSE NoTask

InternalOf(t) ==
    \/ (t \in UserTasks) /\
        (\/ E_Check(t) \/ E_Create(t) \/ E_SetRoot(t) \/ E_RescanInit(t)
         \/ E_ZTLock(t) \/ E_ZTUnlock(t) \/ E_Queue(t)
         \/ D_Check(t) \/ D_ClearEnabled(t) \/ D_WaitEnter(t) \/ D_WaitRead(t)
         \/ D_WaitBlocked(t) \/ D_WaitDone(t) \/ D_Trans(t) \/ D_ClearRoot(t)
         \/ D_FreeLock(t) \/ D_FreeDo(t) \/ D_Clean(t)
         \/ R_Init(t) \/ R_Commit(t) \/ R_ZTLock(t) \/ R_ZTUnlock(t) \/ R_Queue(t))
    \* NB: the standalone btrfs_qgroup_wait_for_completion path (UserWait*/
    \* U_Wait*) is intentionally excluded here. It starts from "idle", so
    \* including it would let an idle task spuriously enter a wait it never
    \* performed and then be unable to start the operation the trace shows.
    \* This workload issues no `quota rescan -w`, so the path is unobserved.
    \/ (t = Worker) /\ (W_ExitLoop \/ W_Finish)

\* The one anticipatory cross-task step: enqueue the rescan work. This sets
\* workerQueued, enabling the worker's RescanWorker_Enter, which can occur
\* before the queueing ioctl returns (its Done event comes later in the
\* trace). Any OTHER hidden cross-task dependency would deadlock TLC.
Enqueue == \E t \in UserTasks : E_Queue(t) \/ R_Queue(t)

TNext ==
    \/ /\ idx <= Len(Trace)
       /\ Observable(Trace[idx].task, Trace[idx].action)
       /\ idx' = idx + 1
    \/ /\ idx <= Len(Trace)
       /\ (InternalOf(NextTask) \/ Enqueue)
       /\ UNCHANGED idx

TSpec == TInit /\ [][TNext]_tvars

\* Violated exactly when the full trace has been replayed => success.
TraceNotDone == idx <= Len(Trace)

(***************************************************************************)
(* Witness probes (see the *_probe_*.cfg files): each is a NEGATED         *)
(* reachability question, so "Invariant X is violated" means the trace     *)
(* DID exercise that window, and "Invariant TraceNotDone is violated"      *)
(* means the trace replayed fully without ever entering it. Used to check  *)
(* whether the workload reached the CVE-relevant interleavings at all —    *)
(* action-level coverage cannot see cross-task state overlap.              *)
(***************************************************************************)

\* CVE-2025-39759 window: one task inside disable's wait_for_completion
\* while another sits in the rescan ioctl's transaction-commit window
\* (FLAG_RESCAN set, rescan_running still FALSE).
NoDisableWaitDuringRescanCommit ==
    ~(\E t1, t2 \in UserTasks :
        t1 # t2 /\ pc[t1] = "r_commit"
                /\ pc[t2] \in {"d_wait_read", "d_wait_block", "d_wait_done"})

\* Proximity to the UAF itself: the free loop runs while any other task
\* holds a live iterator into the qgroup tree.
NoFreeWhileOtherIterates ==
    ~(\E t \in UserTasks :
        pc[t] \in {"d_free_enter", "d_free_lock", "d_free_do"}
        /\ (iterating \ {t}) # {})

================================================================================
