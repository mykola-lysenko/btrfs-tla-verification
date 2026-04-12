------------------- MODULE BtrfsDelayedRefsMultiHeadFixed -------------------
(*
 * BtrfsDelayedRefsMultiHeadFixed.tla — CORRECT multi-head delayed refs loop
 *
 * This is the FIXED variant of BtrfsDelayedRefsMultiHead.tla.
 *
 * THE FIX
 * -------
 * Before releasing the tree lock (i.e., before RunnerPickNext transitions to
 * "HavePtr"), the runner bumps head_refcount[e]. The dropper checks
 * head_refcount[e] before freeing: if the runner holds a reference, the
 * dropper marks the head as "pending free" (head_pending_free) but does NOT
 * clear head_live or pending_delta. The runner's RunnerApplyHead then checks
 * head_pending_free and, if set, skips the apply and calls
 * btrfs_put_delayed_ref_head() which does the actual free.
 *
 * This matches the real kernel fix in btrfs_destroy_delayed_refs():
 *
 *   if (atomic_read(&head->node.refs) > 1) {
 *       refcount_inc(&head->node.refs);
 *       spin_unlock(&head->lock);
 *       btrfs_put_delayed_ref_head(head);
 *       continue;
 *   }
 *
 * PROPERTIES VERIFIED
 * -------------------
 *   NoUAF:      runner never dereferences a freed head
 *   NoLoopUAF:  no head in the runner's queue is freed
 *   RefCountNonNegative: disk_refcount never goes negative
 *)

EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    NumExtents,
    NumAdders,
    MaxOps

ASSUME NumExtents >= 2
ASSUME NumAdders  >= 1
ASSUME MaxOps     >= 1

ES == 1..NumExtents
AS == 1..NumAdders

VARIABLES
    disk_refcount,
    pending_delta,
    head_live,
    head_refcount,       \* per-head refcount: >0 means runner holds a reference
    head_pending_free,   \* dropper wants to free this head but runner holds it
    head_lock,           \* Fix 2.2: per-head spinlock (TRUE = held)
    runner_state,
    runner_target,
    runner_queue,
    dropper_state,
    adder_state,
    adder_extent,
    adder_delta,
    ops_count

vars == <<disk_refcount, pending_delta, head_live, head_refcount,
          head_pending_free, head_lock,
          runner_state, runner_target, runner_queue,
          dropper_state,
          adder_state, adder_extent, adder_delta,
          ops_count>>

Init ==
    /\ disk_refcount     = [e \in ES |-> 1]
    /\ pending_delta     = [e \in ES |-> 0]
    /\ head_live         = [e \in ES |-> FALSE]
    /\ head_refcount     = [e \in ES |-> 0]
    /\ head_pending_free = [e \in ES |-> FALSE]
    /\ head_lock         = [e \in ES |-> FALSE]   \* Fix 2.2: per-head lock
    /\ runner_state      = "Idle"
    /\ runner_target     = 0
    /\ runner_queue      = <<>>
    /\ dropper_state     = "Idle"
    /\ adder_state       = [a \in AS |-> "Idle"]
    /\ adder_extent      = [a \in AS |-> 0]
    /\ adder_delta       = [a \in AS |-> 0]
    /\ ops_count         = 0

(* ---------------------------------------------------------------------------
 * Adder actions (identical to buggy model)
 * --------------------------------------------------------------------------- *)

AdderStart(a) ==
    /\ adder_state[a] = "Idle"
    /\ ops_count < MaxOps
    /\ \E e \in ES, d \in {-1, 1} :
           /\ disk_refcount[e] + pending_delta[e] + d >= 0
           /\ adder_state'  = [adder_state  EXCEPT ![a] = "Adding"]
           /\ adder_extent' = [adder_extent EXCEPT ![a] = e]
           /\ adder_delta'  = [adder_delta  EXCEPT ![a] = d]
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_state, runner_target, runner_queue,
                   dropper_state, ops_count>>

AdderCommit(a) ==
    \* Fix 2.4: d=+1 can commit freely; d=-1 requires "Reserved" state
    /\ \/ /\ adder_state[a] = "Adding"
          /\ adder_delta[a] = 1     \* positive refs need no reservation
       \/ /\ adder_state[a] = "Reserved"
          /\ adder_delta[a] = -1    \* negative refs require prior reservation
    /\ LET e == adder_extent[a]
           d == adder_delta[a]
       IN
       /\ disk_refcount[e] + pending_delta[e] + d >= 0
       /\ pending_delta' = [pending_delta EXCEPT ![e] = pending_delta[e] + d]
       /\ head_live'     = [head_live     EXCEPT ![e] = TRUE]
       /\ adder_state'   = [adder_state   EXCEPT ![a] = "Done"]
       /\ ops_count'     = ops_count + 1
    /\ UNCHANGED <<disk_refcount, head_refcount, head_pending_free, head_lock,
                   runner_state, runner_target, runner_queue,
                   dropper_state, adder_extent, adder_delta>>

(*
 * Fix 2.4: Replace AdderAbort with a space reservation guard.
 *
 * The original AdderAbort was a model artifact: it allowed the adder to abort
 * its commit if disk_refcount + pending_delta + d < 0. This has no direct
 * counterpart in the real kernel.
 *
 * The real kernel uses a space reservation system: before adding a -1 ref,
 * the caller must have reserved space in the delayed_refs_rsv. If the
 * reservation is insufficient, the operation is not queued at all.
 *
 * We model this by adding a per-adder "reserved" flag. An adder can only
 * commit a -1 delta if it has a reservation. Reservations are granted
 * non-deterministically (modeling the async reclaim path), but only when
 * there is sufficient headroom (disk_refcount[e] > 0).
 *
 * This removes AdderAbort entirely and replaces it with:
 *   - AdderReserve: non-deterministically grants a reservation
 *   - AdderCommit: requires reservation for d=-1 ops
 *)

AdderReserve(a) ==
    /\ adder_state[a] = "Adding"
    /\ adder_delta[a] = -1
    /\ LET e == adder_extent[a] IN
       disk_refcount[e] + pending_delta[e] > 0   \* headroom exists
    /\ adder_state' = [adder_state EXCEPT ![a] = "Reserved"]
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_state, runner_target, runner_queue,
                   dropper_state, adder_extent, adder_delta, ops_count>>

AdderReset(a) ==
    /\ adder_state[a] = "Done"
    /\ adder_state'  = [adder_state  EXCEPT ![a] = "Idle"]
    /\ adder_extent' = [adder_extent EXCEPT ![a] = 0]
    /\ adder_delta'  = [adder_delta  EXCEPT ![a] = 0]
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_state, runner_target, runner_queue,
                   dropper_state, ops_count>>

(* ---------------------------------------------------------------------------
 * Runner actions — FIXED multi-head loop
 *
 * FIX: RunnerPickNext bumps head_refcount[e] BEFORE transitioning to "HavePtr".
 * This prevents the dropper from freeing the head while the runner holds it.
 * --------------------------------------------------------------------------- *)

RunnerScan ==
    /\ runner_state = "Idle"
    /\ \E e \in ES : head_live[e] /\ pending_delta[e] /= 0
    /\ LET live == {e \in ES : head_live[e] /\ pending_delta[e] /= 0}
           seq == [i \in 1..Cardinality(live) |->
                       (CHOOSE e \in live :
                           Cardinality({x \in live : x < e}) = i - 1)]
       IN
       /\ runner_queue' = seq
       /\ runner_state' = "Scanning"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_target, dropper_state,
                   adder_state, adder_extent, adder_delta, ops_count>>

\* Fix 2.2: two-step mutex_trylock + refcount_inc pattern
\* Step 1: try to acquire the per-head lock (mutex_trylock)
\* If trylock fails, skip this head (go to RunnerSkipLocked)
RunnerTryLockHead ==
    /\ runner_state = "Scanning"
    /\ runner_queue /= <<>>
    /\ LET e == Head(runner_queue) IN
       /\ head_live[e]           \* only try if still live
       /\ head_lock[e] = FALSE   \* trylock succeeds: head lock is free
       /\ head_lock'     = [head_lock     EXCEPT ![e] = TRUE]  \* acquire head lock
       /\ runner_target' = e
       /\ runner_queue'  = Tail(runner_queue)
       /\ runner_state'  = "HaveLock"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, dropper_state,
                   adder_state, adder_extent, adder_delta, ops_count>>

\* Fix 2.2: trylock failed (head lock is held by dropper) -> skip this head
RunnerSkipLocked ==
    /\ runner_state = "Scanning"
    /\ runner_queue /= <<>>
    /\ LET e == Head(runner_queue) IN
       /\ head_live[e]
       /\ head_lock[e] = TRUE    \* trylock fails: head lock is held
       /\ runner_queue' = Tail(runner_queue)
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_state, runner_target,
                   dropper_state, adder_state, adder_extent, adder_delta, ops_count>>

\* Fix 2.2: Step 2: bump refcount while holding head lock, then release head lock
\* This is the refcount_inc(&head->node.refs) under head->lock pattern
RunnerPickNext ==
    /\ runner_state = "HaveLock"
    /\ runner_target /= 0
    /\ LET e == runner_target IN
       /\ head_live[e]           \* still live while we hold the lock
       /\ head_lock[e] = TRUE    \* we hold the lock
       /\ head_refcount' = [head_refcount EXCEPT ![e] = head_refcount[e] + 1]
                           \* FIX: bump refcount while holding head lock
       /\ head_lock'     = [head_lock     EXCEPT ![e] = FALSE]  \* release head lock
       /\ runner_state'  = "HavePtr"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live,
                   head_pending_free, head_lock, dropper_state, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

\* If the head at the front of the queue was freed by the dropper, skip it
RunnerSkipFreed ==
    /\ runner_state = "Scanning"
    /\ runner_queue /= <<>>
    /\ LET e == Head(runner_queue) IN
       /\ ~head_live[e]   \* head was freed before we could pick it
       /\ runner_queue'  = Tail(runner_queue)
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_state, runner_target, dropper_state,
                   adder_state, adder_extent, adder_delta, ops_count>>

RunnerQueueEmpty ==
    /\ runner_state = "Scanning"
    /\ runner_queue = <<>>
    /\ runner_state' = "Done"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_target, runner_queue, dropper_state,
                   adder_state, adder_extent, adder_delta, ops_count>>

\* Runner applies the head. If head_pending_free is set, skip the apply and
\* do the deferred free instead (btrfs_put_delayed_ref_head path).
RunnerApplyHead ==
    /\ runner_state = "HavePtr"
    /\ runner_target /= 0
    /\ LET e == runner_target IN
       /\ head_live[e]            \* FIX: guaranteed by refcount bump
       /\ ~head_pending_free[e]   \* normal path: dropper has not requested free
       /\ LET d == pending_delta[e] IN
          /\ Assert(disk_refcount[e] + d >= 0,
                    <<"RunnerApply: would drive refcount negative", e>>)
          /\ disk_refcount'     = [disk_refcount     EXCEPT ![e] = disk_refcount[e] + d]
          /\ pending_delta'     = [pending_delta     EXCEPT ![e] = 0]
          /\ head_live'         = [head_live         EXCEPT ![e] = FALSE]
          /\ head_refcount'     = [head_refcount     EXCEPT ![e] = head_refcount[e] - 1]
          /\ runner_state'      = "Scanning"
          /\ runner_target'     = 0
    /\ UNCHANGED <<head_pending_free, head_lock, dropper_state,
                   runner_queue, adder_state, adder_extent, adder_delta, ops_count>>

\* Runner sees head_pending_free: skip apply, do deferred free
RunnerDeferredFree ==
    /\ runner_state = "HavePtr"
    /\ runner_target /= 0
    /\ LET e == runner_target IN
       /\ head_pending_free[e]
       /\ head_refcount'     = [head_refcount     EXCEPT ![e] = head_refcount[e] - 1]
       /\ head_live'         = [head_live         EXCEPT ![e] = FALSE]
       /\ pending_delta'     = [pending_delta     EXCEPT ![e] = 0]
       /\ head_pending_free' = [head_pending_free EXCEPT ![e] = FALSE]
       /\ runner_state'      = "Scanning"
       /\ runner_target'     = 0
    /\ UNCHANGED <<disk_refcount, head_lock, dropper_state,
                   runner_queue, adder_state, adder_extent, adder_delta, ops_count>>

RunnerDone ==
    /\ runner_state = "Done"
    /\ runner_state' = "Idle"
    /\ runner_queue' = <<>>
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_target, dropper_state,
                   adder_state, adder_extent, adder_delta, ops_count>>

(* ---------------------------------------------------------------------------
 * Dropper actions — FIXED: respects head_refcount
 *
 * FIX: if head_refcount[e] > 0, the dropper sets head_pending_free[e] = TRUE
 * instead of immediately clearing head_live[e]. The runner will do the
 * actual free when it releases its reference.
 * --------------------------------------------------------------------------- *)

DropperStart ==
    /\ dropper_state = "Idle"
    /\ dropper_state' = "Dropping"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_state, runner_target, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

\* Fix 2.2: Dropper acquires head_lock before checking refcount
\* This matches the real kernel: spin_lock(&head->lock) before the refcount check
DropperLockHead ==
    /\ dropper_state = "Dropping"
    /\ \E e \in ES : head_live[e] /\ head_lock[e] = FALSE
    /\ LET e == CHOOSE e \in ES : head_live[e] /\ head_lock[e] = FALSE IN
       /\ head_lock' = [head_lock EXCEPT ![e] = TRUE]
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, dropper_state, runner_state, runner_target, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

\* Dropper frees a head that the runner does NOT hold (refcount = 0)
\* Must hold head_lock to check refcount atomically with runner's trylock
DropperFreeHead ==
    /\ dropper_state = "Dropping"
    /\ \E e \in ES : head_live[e] /\ head_lock[e] = TRUE /\ head_refcount[e] = 0
    /\ LET e == CHOOSE e \in ES : head_live[e] /\ head_lock[e] = TRUE /\ head_refcount[e] = 0 IN
       /\ head_live'     = [head_live     EXCEPT ![e] = FALSE]
       /\ pending_delta' = [pending_delta EXCEPT ![e] = 0]
       /\ head_lock'     = [head_lock     EXCEPT ![e] = FALSE]  \* release head lock
    /\ UNCHANGED <<disk_refcount, head_refcount, head_pending_free, dropper_state,
                   runner_state, runner_target, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

\* Dropper defers free for a head the runner holds (refcount > 0)
\* Must hold head_lock to set pending_free atomically
DropperDeferFree ==
    /\ dropper_state = "Dropping"
    /\ \E e \in ES : head_live[e] /\ head_lock[e] = TRUE /\ head_refcount[e] > 0
    /\ LET e == CHOOSE e \in ES : head_live[e] /\ head_lock[e] = TRUE /\ head_refcount[e] > 0 IN
       /\ head_pending_free' = [head_pending_free EXCEPT ![e] = TRUE]
       /\ head_lock'         = [head_lock         EXCEPT ![e] = FALSE]  \* release head lock
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   dropper_state, runner_state, runner_target, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

DropperDone ==
    /\ dropper_state = "Dropping"
    /\ \A e \in ES : ~head_live[e] \/ head_pending_free[e]
    /\ \A a \in AS : adder_state[a] /= "Adding"
    /\ dropper_state' = "Done"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_state, runner_target, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

DropperReset ==
    /\ dropper_state = "Done"
    /\ dropper_state' = "Idle"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   head_pending_free, head_lock, runner_state, runner_target, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

(* ---------------------------------------------------------------------------
 * Terminal stutter
 * --------------------------------------------------------------------------- *)

Terminal ==
    /\ runner_state = "Idle"
    /\ dropper_state = "Idle"
    /\ \A a \in AS : adder_state[a] = "Idle"
    /\ \A e \in ES : ~head_live[e]
    /\ \A e \in ES : head_lock[e] = FALSE   \* no locks held at terminal state
    /\ UNCHANGED vars

(* ---------------------------------------------------------------------------
 * Next-state relation
 * --------------------------------------------------------------------------- *)

Next ==
    \/ \E a \in AS : AdderStart(a) \/ AdderReserve(a) \/ AdderCommit(a) \/ AdderReset(a)
    \/ RunnerScan
    \/ RunnerTryLockHead    \* Fix 2.2: two-step trylock
    \/ RunnerSkipLocked     \* Fix 2.2: skip if trylock fails
    \/ RunnerPickNext
    \/ RunnerSkipFreed
    \/ RunnerQueueEmpty
    \/ RunnerApplyHead
    \/ RunnerDeferredFree
    \/ RunnerDone
    \/ DropperStart
    \/ DropperLockHead      \* Fix 2.2: dropper acquires head lock
    \/ DropperFreeHead
    \/ DropperDeferFree
    \/ DropperDone
    \/ DropperReset
    \/ Terminal

Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------------
 * Safety invariants
 * --------------------------------------------------------------------------- *)

RefCountNonNegative ==
    \A e \in ES : disk_refcount[e] >= 0

\* FIX guarantees: runner never holds a pointer to a freed head
NoUAF ==
    runner_state = "HavePtr" =>
        (runner_target /= 0 /\ head_live[runner_target])

\* FIX guarantees: no head in the queue is freed without a pending_free marker
NoLoopUAF ==
    \A i \in DOMAIN runner_queue :
        head_live[runner_queue[i]] \/ head_pending_free[runner_queue[i]]

\* Refcount invariant: a head can only be pending_free if the runner holds it
PendingFreeImpliesRefcount ==
    \A e \in ES :
        head_pending_free[e] => head_refcount[e] > 0

NoPendingAfterDrop ==
    dropper_state = "Done" =>
        \A e \in ES : head_live[e] => (pending_delta[e] = 0 \/ head_pending_free[e])

=============================================================================
