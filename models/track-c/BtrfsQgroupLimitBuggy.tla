----------------------- MODULE BtrfsQgroupLimitBuggy -----------------------
EXTENDS Integers, TLC

(*
 * BtrfsQgroupLimitBuggy.tla
 *
 * THE BUG: The qgroup_lock is released between the limit check and the
 * reservation increment. This creates a TOCTOU window:
 *
 * 1. Alloc1 checks: rsv_bytes + 6 = 6 <= 10 (OK)
 * 2. Alloc2 checks: rsv_bytes + 6 = 6 <= 10 (OK, same stale value)
 * 3. Alloc1 increments: rsv_bytes = 6
 * 4. Alloc2 increments: rsv_bytes = 12 > max_limit = 10
 * 5. VIOLATION: NoLimitExceeded fails
 *)

VARIABLES
    rsv_bytes,
    max_limit,
    alloc1_state,
    alloc2_state

vars == <<rsv_bytes, max_limit, alloc1_state, alloc2_state>>

Init ==
    /\ rsv_bytes = 0
    /\ max_limit = 10
    /\ alloc1_state = "IDLE"
    /\ alloc2_state = "IDLE"

-----------------------------------------------------------------------------
\* ALLOCATOR 1 (BUGGY: check and increment are separate steps, no lock held)

Alloc1Check ==
    /\ alloc1_state = "IDLE"
    /\ rsv_bytes + 6 <= max_limit  \* BUG: check without lock
    /\ alloc1_state' = "CHECKED"
    /\ UNCHANGED <<rsv_bytes, max_limit, alloc2_state>>

Alloc1Inc ==
    /\ alloc1_state = "CHECKED"
    \* BUG: no re-check, no lock held
    /\ rsv_bytes' = rsv_bytes + 6
    /\ alloc1_state' = "ALLOCATED"
    /\ UNCHANGED <<max_limit, alloc2_state>>

Alloc1Finish ==
    /\ alloc1_state = "ALLOCATED"
    /\ alloc1_state' = "DONE"
    /\ UNCHANGED <<rsv_bytes, max_limit, alloc2_state>>

-----------------------------------------------------------------------------
\* ALLOCATOR 2 (BUGGY: same pattern)

Alloc2Check ==
    /\ alloc2_state = "IDLE"
    /\ rsv_bytes + 6 <= max_limit  \* BUG: check without lock
    /\ alloc2_state' = "CHECKED"
    /\ UNCHANGED <<rsv_bytes, max_limit, alloc1_state>>

Alloc2Inc ==
    /\ alloc2_state = "CHECKED"
    \* BUG: no re-check, no lock held
    /\ rsv_bytes' = rsv_bytes + 6
    /\ alloc2_state' = "ALLOCATED"
    /\ UNCHANGED <<max_limit, alloc1_state>>

Alloc2Finish ==
    /\ alloc2_state = "ALLOCATED"
    /\ alloc2_state' = "DONE"
    /\ UNCHANGED <<rsv_bytes, max_limit, alloc1_state>>

-----------------------------------------------------------------------------

Next ==
    \/ Alloc1Check
    \/ Alloc1Inc
    \/ Alloc1Finish
    \/ Alloc2Check
    \/ Alloc2Inc
    \/ Alloc2Finish

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* PROPERTIES

NoLimitExceeded ==
    rsv_bytes <= max_limit

=============================================================================
