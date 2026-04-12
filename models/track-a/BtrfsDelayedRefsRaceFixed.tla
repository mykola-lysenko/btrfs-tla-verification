------------------------ MODULE BtrfsDelayedRefsRaceFixed ------------------------
EXTENDS Integers, FiniteSets, TLC

(*
 * BtrfsDelayedRefsRaceFixed.tla — Corrected concurrent run/drop model
 *
 * Identical to BtrfsDelayedRefsRace.tla except that RunnerReadHead now
 * bumps head_refcount[e] before releasing the delayed_refs->lock.
 * DropperFreeHead is blocked from freeing a head whose refcount > 0.
 * RunnerApplyHead decrements the refcount after applying.
 *
 * A global MaxOps bound prevents unbounded adder cycling.
 *)

CONSTANTS
    NumExtents,
    NumAdders,
    MaxOps

ASSUME NumExtents >= 1
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
    dropper_state,
    adder_state,
    adder_extent,
    adder_delta,
    ops_count

vars == <<disk_refcount, pending_delta, head_live, head_refcount,
          runner_state, runner_target,
          dropper_state,
          adder_state, adder_extent, adder_delta,
          ops_count>>

-----------------------------------------------------------------------------
Init ==
    /\ disk_refcount = [e \in ES |-> 1]
    /\ pending_delta = [e \in ES |-> 0]
    /\ head_live     = [e \in ES |-> FALSE]
    /\ head_refcount = [e \in ES |-> 0]
    /\ runner_state  = "Idle"
    /\ runner_target = 0
    /\ dropper_state = "Idle"
    /\ adder_state   = [a \in AS |-> "Idle"]
    /\ adder_extent  = [a \in AS |-> 0]
    /\ adder_delta   = [a \in AS |-> 0]
    /\ ops_count     = 0

-----------------------------------------------------------------------------
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
                   runner_state, runner_target, dropper_state, ops_count>>

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
    /\ UNCHANGED <<disk_refcount, head_refcount, runner_state, runner_target, dropper_state,
                   adder_extent, adder_delta>>

AdderReset(a) ==
    /\ adder_state[a] = "Done"
    /\ adder_state'  = [adder_state  EXCEPT ![a] = "Idle"]
    /\ adder_extent' = [adder_extent EXCEPT ![a] = 0]
    /\ adder_delta'  = [adder_delta  EXCEPT ![a] = 0]
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_state, runner_target, dropper_state, ops_count>>

-----------------------------------------------------------------------------
\* RUNNER (FIXED): bump head_refcount before releasing lock

RunnerReadHead ==
    /\ runner_state = "Idle"
    /\ dropper_state = "Idle"
    /\ \E e \in ES : head_live[e] /\ pending_delta[e] /= 0
    /\ LET e == CHOOSE e \in ES : head_live[e] /\ pending_delta[e] /= 0 IN
       /\ runner_target'  = e
       /\ runner_state'   = "HavePtr"
       \* FIX: bump refcount before releasing the lock
       /\ head_refcount'  = [head_refcount EXCEPT ![e] = head_refcount[e] + 1]
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live,
                   dropper_state, adder_state, adder_extent, adder_delta, ops_count>>

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
       \* FIX: decrement refcount after applying
       /\ head_refcount' = [head_refcount EXCEPT ![e] = head_refcount[e] - 1]
       /\ runner_state'  = "Done"
       /\ runner_target' = 0
    /\ UNCHANGED <<dropper_state, adder_state, adder_extent, adder_delta, ops_count>>

RunnerDone ==
    /\ runner_state = "Done"
    /\ runner_state' = "Idle"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_target, dropper_state, adder_state, adder_extent, adder_delta, ops_count>>

-----------------------------------------------------------------------------
\* DROPPER (FIXED): cannot free a head whose refcount > 0

DropperStart ==
    /\ dropper_state = "Idle"
    /\ dropper_state' = "Dropping"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_state, runner_target, adder_state, adder_extent, adder_delta, ops_count>>

DropperFreeHead ==
    /\ dropper_state = "Dropping"
    \* FIX: only free heads with refcount = 0
    /\ \E e \in ES : head_live[e] /\ head_refcount[e] = 0
    /\ LET e == CHOOSE e \in ES : head_live[e] /\ head_refcount[e] = 0 IN
       /\ head_live'     = [head_live     EXCEPT ![e] = FALSE]
       /\ pending_delta' = [pending_delta EXCEPT ![e] = 0]
    /\ UNCHANGED <<disk_refcount, head_refcount, dropper_state,
                   runner_state, runner_target, adder_state, adder_extent, adder_delta, ops_count>>

DropperDone ==
    /\ dropper_state = "Dropping"
    /\ ~(\E e \in ES : head_live[e] /\ head_refcount[e] = 0)
    /\ dropper_state' = "Done"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_state, runner_target, adder_state, adder_extent, adder_delta, ops_count>>

DropperReset ==
    /\ dropper_state = "Done"
    /\ dropper_state' = "Idle"
    /\ UNCHANGED <<disk_refcount, pending_delta, head_live, head_refcount,
                   runner_state, runner_target, adder_state, adder_extent, adder_delta, ops_count>>

-----------------------------------------------------------------------------
Terminal ==
    /\ runner_state = "Idle"
    /\ dropper_state = "Idle"
    /\ \A a \in AS : adder_state[a] = "Idle"
    /\ \A e \in ES : ~head_live[e]
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
Next ==
    \/ \E a \in AS : AdderStart(a) \/ AdderCommit(a) \/ AdderReset(a)
    \/ RunnerReadHead
    \/ RunnerApplyHead
    \/ RunnerDone
    \/ DropperStart
    \/ DropperFreeHead
    \/ DropperDone
    \/ DropperReset
    \/ Terminal

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
RefCountNonNegative ==
    \A e \in ES : disk_refcount[e] >= 0

NoPendingAfterDrop ==
    \* After dropper finishes, freed heads must have zero pending delta
    dropper_state = "Done" =>
        \A e \in ES : ~head_live[e] => pending_delta[e] = 0

NoUAF ==
    runner_state = "HavePtr" =>
        (runner_target /= 0 /\ head_live[runner_target])

=============================================================================
