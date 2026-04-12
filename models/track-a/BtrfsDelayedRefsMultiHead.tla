--------------------- MODULE BtrfsDelayedRefsMultiHead ---------------------
(*
 * BtrfsDelayedRefsMultiHead.tla — BUGGY multi-head delayed refs loop race
 *
 * BACKGROUND
 * ----------
 * The real btrfs_run_delayed_refs() processes delayed ref heads in a loop:
 *
 *   while ((node = rb_first(&delayed_refs->href_root))) {
 *       head = rb_entry(node, ...);
 *       spin_lock(&head->lock);
 *       spin_unlock(&delayed_refs->lock);   <-- releases the tree lock
 *       ret = run_one_delayed_ref(..., head, ...);
 *       btrfs_delayed_ref_unlock(head);
 *       btrfs_put_delayed_ref_head(head);
 *       spin_lock(&delayed_refs->lock);     <-- re-acquires tree lock
 *   }
 *
 * THE MULTI-HEAD RACE
 * -------------------
 * The runner processes N heads in a loop. After applying head[i], it
 * re-acquires the tree lock and picks the next head. The dropper can free
 * ANY head at ANY point.
 *
 * New bug surface vs. single-head model:
 *   1. Runner builds a queue of heads [h1, h2, h3].
 *   2. Runner picks h1, releases tree lock.
 *   3. Dropper frees h1 AND h2 while runner is between lock release and apply.
 *   4. Runner applies h1 (UAF on h1 — NoUAF fires).
 *   5. Runner re-acquires tree lock, tries to pick h2 from its queue.
 *   6. h2 is already freed — NoLoopUAF fires.
 *
 * BUG: runner does NOT bump head_refcount before releasing the tree lock.
 *
 * CORRECT FIX: BtrfsDelayedRefsMultiHeadFixed.tla
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
    head_refcount,
    runner_state,
    runner_target,
    runner_queue,
    dropper_state,
    adder_state,
    adder_extent,
    adder_delta,
    ops_count

vars == <<disk_refcount, pending_delta, head_live, head_refcount,
          runner_state, runner_target, runner_queue,
          dropper_state,
          adder_state, adder_extent, adder_delta,
          ops_count>>

Init ==
    /\ disk_refcount = [e \in ES |-> 1]
    /\ pending_delta = [e \in ES |-> 0]
    /\ head_live     = [e \in ES |-> FALSE]
    /\ head_refcount = [e \in ES |-> 0]
    /\ runner_state  = "Idle"
    /\ runner_target = 0
    /\ runner_queue  = <<>>
    /\ dropper_state = "Idle"
    /\ adder_state   = [a \in AS |-> "Idle"]
    /\ adder_extent  = [a \in AS |-> 0]
    /\ adder_delta   = [a \in AS |-> 0]
    /\ ops_count     = 0

(* ---------------------------------------------------------------------------
 * Adder actions
 * --------------------------------------------------------------------------- *)

AdderStart(a) ==
    /\ adder_state[a] = "Idle"
    /\ dropper_state = "Idle"
    /\ ops_count < MaxOps
    /\ \E e \in ES, d \in {-1, 1} :
           /\ disk_refcount[e] + pending_delta[e] + d >= 0
           /\ adder_state'  = [adder_state  EXCEPT ![a] = "Adding"]
           /\ adder_extent' = [adder_extent EXCEPT ![a] = e]
           /\ adder_delta'  = [adder_delta  EXCEPT ![a] = d]
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_state, runner_target, runner_queue,
                   dropper_state, ops_count>>

AdderCommit(a) ==
    /\ adder_state[a] = "Adding"
    /\ LET e == adder_extent[a]
           d == adder_delta[a]
       IN
       /\ disk_refcount[e] + pending_delta[e] + d >= 0
       /\ pending_delta' = [pending_delta EXCEPT ![e] = pending_delta[e] + d]
       /\ head_live'     = [head_live     EXCEPT ![e] = TRUE]
       /\ adder_state'   = [adder_state   EXCEPT ![a] = "Done"]
       /\ ops_count'     = ops_count + 1
    /\ UNCHANGED <<disk_refcount, head_refcount,
                   runner_state, runner_target, runner_queue,
                   dropper_state, adder_extent, adder_delta>>

AdderReset(a) ==
    /\ adder_state[a] = "Done"
    /\ adder_state'  = [adder_state  EXCEPT ![a] = "Idle"]
    /\ adder_extent' = [adder_extent EXCEPT ![a] = 0]
    /\ adder_delta'  = [adder_delta  EXCEPT ![a] = 0]
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_state, runner_target, runner_queue,
                   dropper_state, ops_count>>

(* ---------------------------------------------------------------------------
 * Runner actions — BUGGY multi-head loop
 * BUG: RunnerPickNext does NOT bump head_refcount before releasing tree lock
 * --------------------------------------------------------------------------- *)

RunnerScan ==
    /\ runner_state = "Idle"
    /\ dropper_state = "Idle"
    /\ \E e \in ES : head_live[e] /\ pending_delta[e] /= 0
    /\ LET live == {e \in ES : head_live[e] /\ pending_delta[e] /= 0}
           seq == [i \in 1..Cardinality(live) |->
                       (CHOOSE e \in live :
                           Cardinality({x \in live : x < e}) = i - 1)]
       IN
       /\ runner_queue' = seq
       /\ runner_state' = "Scanning"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_target, dropper_state,
                   adder_state, adder_extent, adder_delta, ops_count>>

RunnerPickNext ==
    /\ runner_state = "Scanning"
    /\ runner_queue /= <<>>
    /\ LET e == Head(runner_queue) IN
       /\ runner_target' = e
       /\ runner_queue'  = Tail(runner_queue)
       /\ runner_state'  = "HavePtr"
       \* BUG: no head_refcount[e] bump here
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   dropper_state, adder_state, adder_extent, adder_delta, ops_count>>

RunnerQueueEmpty ==
    /\ runner_state = "Scanning"
    /\ runner_queue = <<>>
    /\ runner_state' = "Done"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_target, runner_queue, dropper_state,
                   adder_state, adder_extent, adder_delta, ops_count>>

RunnerApplyHead ==
    /\ runner_state = "HavePtr"
    /\ runner_target /= 0
    /\ LET e == runner_target
           d == pending_delta[e]
       IN
       /\ Assert(head_live[e],
                 <<"UAF: runner applied a freed delayed-ref head", e>>)
       /\ Assert(disk_refcount[e] + d >= 0,
                 <<"RunnerApply: would drive refcount negative", e, disk_refcount[e], d>>)
       /\ disk_refcount' = [disk_refcount EXCEPT ![e] = disk_refcount[e] + d]
       /\ pending_delta' = [pending_delta EXCEPT ![e] = 0]
       /\ head_live'     = [head_live     EXCEPT ![e] = FALSE]
       /\ runner_state'  = "Scanning"
       /\ runner_target' = 0
    /\ UNCHANGED <<head_refcount, dropper_state,
                   runner_queue, adder_state, adder_extent, adder_delta, ops_count>>

RunnerDone ==
    /\ runner_state = "Done"
    /\ runner_state' = "Idle"
    /\ runner_queue' = <<>>
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_target, dropper_state,
                   adder_state, adder_extent, adder_delta, ops_count>>

(* ---------------------------------------------------------------------------
 * Dropper actions
 * --------------------------------------------------------------------------- *)

DropperStart ==
    /\ dropper_state = "Idle"
    /\ dropper_state' = "Dropping"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_state, runner_target, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

DropperFreeHead ==
    /\ dropper_state = "Dropping"
    /\ \E e \in ES : head_live[e]
    /\ LET e == CHOOSE e \in ES : head_live[e] IN
       /\ head_live'     = [head_live     EXCEPT ![e] = FALSE]
       /\ pending_delta' = [pending_delta EXCEPT ![e] = 0]
    /\ UNCHANGED <<disk_refcount, head_refcount, dropper_state,
                   runner_state, runner_target, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

DropperDone ==
    /\ dropper_state = "Dropping"
    /\ \A e \in ES : ~head_live[e]
    /\ \A a \in AS : adder_state[a] /= "Adding"
    /\ dropper_state' = "Done"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_state, runner_target, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

DropperReset ==
    /\ dropper_state = "Done"
    /\ dropper_state' = "Idle"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_state, runner_target, runner_queue,
                   adder_state, adder_extent, adder_delta, ops_count>>

(* ---------------------------------------------------------------------------
 * Terminal stutter
 * --------------------------------------------------------------------------- *)

Terminal ==
    /\ runner_state = "Idle"
    /\ dropper_state = "Idle"
    /\ \A a \in AS : adder_state[a] = "Idle"
    /\ \A e \in ES : ~head_live[e]
    /\ UNCHANGED vars

(* ---------------------------------------------------------------------------
 * Next-state relation
 * --------------------------------------------------------------------------- *)

Next ==
    \/ \E a \in AS : AdderStart(a) \/ AdderCommit(a) \/ AdderReset(a)
    \/ RunnerScan
    \/ RunnerPickNext
    \/ RunnerQueueEmpty
    \/ RunnerApplyHead
    \/ RunnerDone
    \/ DropperStart
    \/ DropperFreeHead
    \/ DropperDone
    \/ DropperReset
    \/ Terminal

Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------------
 * Safety invariants
 * --------------------------------------------------------------------------- *)

RefCountNonNegative ==
    \A e \in ES : disk_refcount[e] >= 0

NoUAF ==
    runner_state = "HavePtr" =>
        (runner_target /= 0 /\ head_live[runner_target])

NoLoopUAF ==
    \A i \in DOMAIN runner_queue :
        head_live[runner_queue[i]]

NoPendingAfterDrop ==
    dropper_state = "Done" =>
        \A e \in ES : head_live[e] => pending_delta[e] = 0

=============================================================================
