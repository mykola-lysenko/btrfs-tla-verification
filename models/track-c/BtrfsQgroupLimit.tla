----------------------- MODULE BtrfsQgroupLimit -----------------------
EXTENDS Integers, TLC

(*
 * BtrfsQgroupLimit.tla
 *
 * Models the race between subvolume quota limit enforcement
 * (`qgroup_reserve`) and concurrent allocations.
 *
 * The core synchronization is:
 * 1. Allocator takes `qgroup_lock` (spinlock)
 * 2. Calls `qgroup_check_limits`
 * 3. If under limit, calls `qgroup_rsv_add` (increments reservation)
 * 4. Releases `qgroup_lock`
 *)

VARIABLES
    qgroup_lock,    \* 0 = free, 1 = locked
    rsv_bytes,      \* currently reserved bytes
    max_limit,      \* maximum allowed bytes
    alloc1_state,   \* IDLE, LOCKING, CHECKING, ALLOCATED, DONE
    alloc2_state    \* IDLE, LOCKING, CHECKING, ALLOCATED, DONE

vars == <<qgroup_lock, rsv_bytes, max_limit, alloc1_state, alloc2_state>>

Init ==
    /\ qgroup_lock = 0
    /\ rsv_bytes = 0
    /\ max_limit = 10
    /\ alloc1_state = "IDLE"
    /\ alloc2_state = "IDLE"

-----------------------------------------------------------------------------
\* ALLOCATOR 1 (requests 6 bytes)

Alloc1Lock ==
    /\ alloc1_state = "IDLE"
    /\ qgroup_lock = 0
    /\ qgroup_lock' = 1
    /\ alloc1_state' = "CHECKING"
    /\ UNCHANGED <<rsv_bytes, max_limit, alloc2_state>>

Alloc1CheckAndReserve ==
    /\ alloc1_state = "CHECKING"
    /\ qgroup_lock = 1
    /\ IF rsv_bytes + 6 <= max_limit
       THEN /\ rsv_bytes' = rsv_bytes + 6
            /\ alloc1_state' = "ALLOCATED"
       ELSE /\ rsv_bytes' = rsv_bytes
            /\ alloc1_state' = "DONE"
    /\ qgroup_lock' = 0
    /\ UNCHANGED <<max_limit, alloc2_state>>

Alloc1Finish ==
    /\ alloc1_state = "ALLOCATED"
    /\ alloc1_state' = "DONE"
    /\ UNCHANGED <<qgroup_lock, rsv_bytes, max_limit, alloc2_state>>

-----------------------------------------------------------------------------
\* ALLOCATOR 2 (requests 6 bytes)

Alloc2Lock ==
    /\ alloc2_state = "IDLE"
    /\ qgroup_lock = 0
    /\ qgroup_lock' = 1
    /\ alloc2_state' = "CHECKING"
    /\ UNCHANGED <<rsv_bytes, max_limit, alloc1_state>>

Alloc2CheckAndReserve ==
    /\ alloc2_state = "CHECKING"
    /\ qgroup_lock = 1
    /\ IF rsv_bytes + 6 <= max_limit
       THEN /\ rsv_bytes' = rsv_bytes + 6
            /\ alloc2_state' = "ALLOCATED"
       ELSE /\ rsv_bytes' = rsv_bytes
            /\ alloc2_state' = "DONE"
    /\ qgroup_lock' = 0
    /\ UNCHANGED <<max_limit, alloc1_state>>

Alloc2Finish ==
    /\ alloc2_state = "ALLOCATED"
    /\ alloc2_state' = "DONE"
    /\ UNCHANGED <<qgroup_lock, rsv_bytes, max_limit, alloc1_state>>

-----------------------------------------------------------------------------

Next ==
    \/ Alloc1Lock
    \/ Alloc1CheckAndReserve
    \/ Alloc1Finish
    \/ Alloc2Lock
    \/ Alloc2CheckAndReserve
    \/ Alloc2Finish

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* PROPERTIES

\* The total reserved bytes must never exceed the max limit.
NoLimitExceeded ==
    rsv_bytes <= max_limit

=============================================================================
