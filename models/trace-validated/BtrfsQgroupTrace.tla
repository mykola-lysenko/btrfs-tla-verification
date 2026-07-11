--------------------------- MODULE BtrfsQgroupTrace ---------------------------
(***************************************************************************)
(* Trace-validation spec: checks that a real kernel trace (converted by    *)
(* tracing/trace_to_tla.py into BtrfsQgroupTraceData.tla) is an accepted   *)
(* behavior of BtrfsQgroupLifecycle.                                       *)
(*                                                                         *)
(* Each step either (a) matches the next observable trace event and       *)
(* advances idx, or (b) performs an internal (unobserved) model action.    *)
(* Consuming the whole trace violates the pseudo-invariant TraceNotDone.   *)
(*                                                                         *)
(* Some observable events are ambiguous (WaitRescanCompletion_Enter is     *)
(* both the rescan-wait ioctl and close_ctree at unmount), so replay       *)
(* forks branches and wrong branches die in sink states. TLC must run      *)
(* with -deadlock (deadlock checking OFF); the verdict is then:            *)
(*                                                                         *)
(*   "Invariant TraceNotDone is violated" => TRACE ACCEPTED — some branch  *)
(*        consumed the whole trace (success!)                              *)
(*   "No error has been found"            => DIVERGENCE — every branch     *)
(*        got stuck before the end of the trace.                           *)
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
         \/ E_SimpleSkip(t) \/ E_ZTLock(t) \/ E_ZTUnlock(t) \/ E_Queue(t)
         \/ D_Check(t) \/ D_ClearEnabled(t) \/ D_WaitEnter(t) \/ D_WaitRead(t)
         \/ D_WaitBlocked(t) \/ D_WaitDone(t) \/ D_Trans(t) \/ D_ClearRoot(t)
         \/ D_FreeLock(t) \/ D_FreeDo(t) \/ D_Clean(t)
         \/ R_Init(t) \/ R_Commit(t) \/ R_ZTLock(t) \/ R_ZTUnlock(t) \/ R_Queue(t)
         \* standalone wait / unmount: only the mid-operation internals —
         \* their entry points (UserWaitEnter, UmountBegin) are observable,
         \* so an idle task cannot wander into these paths spuriously
         \/ U_WaitRead(t) \/ U_WaitBlocked(t)
         \/ M_WaitRead(t) \/ M_WaitBlocked(t) \/ M_FreeLock(t) \/ M_FreeDo(t))
    \/ (t = Worker) /\ (W_ExitLoop \/ W_Finish)

\* Anticipatory cross-task steps — handoffs whose effect precedes the
\* handing task's next observable event. Two exist in this protocol:
\*   Enqueue: E_Queue/R_Queue set workerQueued, enabling RescanWorker_Enter
\*     before the queueing ioctl returns (its Done event comes later).
\*   WorkerFinish: W_ExitLoop/W_Finish run complete_all INSIDE the worker,
\*     unblocking a waiter's WaitRescanCompletion_Done before the worker's
\*     own RescanWorker_Done (the kretprobe at function exit) appears.
\* Any OTHER hidden cross-task dependency would deadlock TLC.
Enqueue      == \E t \in UserTasks : E_Queue(t) \/ R_Queue(t)
WorkerFinish == W_ExitLoop \/ W_Finish

TNext ==
    \/ /\ idx <= Len(Trace)
       /\ Observable(Trace[idx].task, Trace[idx].action)
       /\ idx' = idx + 1
    \/ /\ idx <= Len(Trace)
       /\ (InternalOf(NextTask) \/ Enqueue \/ WorkerFinish)
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

\* Proximity to the UAF itself: the free loop (from disable OR unmount)
\* runs while any other task holds a live iterator into the qgroup tree.
NoFreeWhileOtherIterates ==
    ~(\E t \in UserTasks :
        pc[t] \in {"d_free_enter", "d_free_lock", "d_free_do",
                   "m_free_enter", "m_free_lock", "m_free_do"}
        /\ (iterating \ {t}) # {})

================================================================================
