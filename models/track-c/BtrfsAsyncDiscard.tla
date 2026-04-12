---------------------------- MODULE BtrfsAsyncDiscard ----------------------------
(*
 * Model: Btrfs async discard race with extent reuse
 *
 * Bug description:
 * Btrfs uses an asynchronous discard mechanism where freed extents are placed
 * on a discard list to be TRIMmed later by a background worker. A race condition
 * occurs if the allocator reuses one of these extents and writes new data to it
 * BEFORE the async discard worker actually issues the TRIM command.
 * If the TRIM command executes after the new data is written, it destroys the
 * newly written data, leading to corruption.
 *
 * Sequence (buggy):
 * 1. Extent is freed and added to async discard list.
 * 2. Allocator allocates the same extent for new data.
 * 3. Allocator writes new data to the extent.
 * 4. Async discard worker issues TRIM on the extent.
 * 5. Result: New data is TRIMmed (destroyed).
 *
 * Fix: The allocator must remove the extent from the async discard list
 * before reusing it, OR the discard worker must re-verify that the extent
 * is still free before issuing the TRIM command. In Btrfs, the allocator
 * removes the extent from the discard state when allocating.
 *
 * Variables:
 *   extent_state: "Allocated" | "Freed" | "DiscardPending"
 *   extent_data: "Valid" | "Trimmed"
 *   alloc_pc: "Init" | "Free" | "Allocate" | "Write" | "Done"
 *   discard_pc: "Init" | "ReadList" | "IssueTrim" | "Done"
 *
 * Invariant: NoDataTrimmed (if extent is Allocated, data must not be Trimmed)
 *)

EXTENDS Integers, TLC

VARIABLES
    extent_state,
    extent_data,
    alloc_pc,
    discard_pc

vars == <<extent_state, extent_data, alloc_pc, discard_pc>>

Init ==
    /\ extent_state = "Allocated"
    /\ extent_data = "Valid"
    /\ alloc_pc = "Init"
    /\ discard_pc = "Init"

(* ===========================================================================
 * BUGGY VARIANT: Allocator reuses extent without removing from discard list
 * =========================================================================== *)

BuggyAllocFree ==
    /\ alloc_pc = "Init"
    /\ extent_state = "Allocated"
    /\ extent_state' = "DiscardPending"
    /\ alloc_pc' = "Allocate"
    /\ UNCHANGED <<extent_data, discard_pc>>

BuggyAllocAllocate ==
    /\ alloc_pc = "Allocate"
    /\ extent_state \in {"Freed", "DiscardPending"}
    \* BUG: Reuses extent but leaves it as DiscardPending if it was
    /\ extent_state' = "Allocated"
    /\ alloc_pc' = "Write"
    /\ UNCHANGED <<extent_data, discard_pc>>

BuggyAllocWrite ==
    /\ alloc_pc = "Write"
    /\ extent_state = "Allocated"
    /\ extent_data' = "Valid"
    /\ alloc_pc' = "Done"
    /\ UNCHANGED <<extent_state, discard_pc>>

BuggyDiscardReadList ==
    /\ discard_pc = "Init"
    \* Discard worker finds extent on list (even if it was re-allocated,
    \* because buggy allocator didn't remove it from the list properly,
    \* modeled here by the worker proceeding if it was EVER DiscardPending.
    \* Actually, simpler: worker just reads the state, and if it's DiscardPending,
    \* it decides to trim. But if it reads DiscardPending and then Alloc reallocates,
    \* it will trim an Allocated extent.
    /\ extent_state = "DiscardPending"
    /\ discard_pc' = "IssueTrim"
    /\ UNCHANGED <<extent_state, extent_data, alloc_pc>>

BuggyDiscardTrim ==
    /\ discard_pc = "IssueTrim"
    /\ extent_data' = "Trimmed"
    /\ extent_state' = IF extent_state = "DiscardPending" THEN "Freed" ELSE extent_state
    /\ discard_pc' = "Done"
    /\ UNCHANGED <<alloc_pc>>

\* Discard worker gives up if extent was already reallocated (no longer DiscardPending)
BuggyDiscardSkip ==
    /\ discard_pc = "Init"
    /\ extent_state /= "DiscardPending"
    /\ discard_pc' = "Done"
    /\ UNCHANGED <<extent_state, extent_data, alloc_pc>>

BuggyDone ==
    /\ alloc_pc = "Done"
    /\ discard_pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyAllocFree
    \/ BuggyAllocAllocate
    \/ BuggyAllocWrite
    \/ BuggyDiscardReadList
    \/ BuggyDiscardTrim
    \/ BuggyDiscardSkip
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyAllocFree)
    /\ WF_vars(BuggyAllocAllocate)
    /\ WF_vars(BuggyAllocWrite)
    /\ WF_vars(BuggyDiscardReadList)
    /\ WF_vars(BuggyDiscardTrim)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Allocator removes extent from discard list (or discard checks)
 * =========================================================================== *)

FixedAllocFree ==
    /\ alloc_pc = "Init"
    /\ extent_state = "Allocated"
    /\ extent_state' = "DiscardPending"
    /\ alloc_pc' = "Allocate"
    /\ UNCHANGED <<extent_data, discard_pc>>

FixedAllocAllocate ==
    /\ alloc_pc = "Allocate"
    /\ extent_state \in {"Freed", "DiscardPending"}
    \* FIX: Allocator explicitly removes from discard list (state becomes Allocated)
    \* AND we model the synchronization where Discard worker cannot be in the middle
    \* of trimming this exact extent. If discard worker already decided to trim
    \* (IssueTrim), allocator must wait or discard worker must re-verify.
    \* In Btrfs, the extent is locked or removed from the tree. We model this
    \* by making the allocator wait if the discard worker is currently processing it.
    /\ discard_pc /= "IssueTrim"
    /\ extent_state' = "Allocated"
    /\ alloc_pc' = "Write"
    /\ UNCHANGED <<extent_data, discard_pc>>

FixedAllocWrite ==
    /\ alloc_pc = "Write"
    /\ extent_state = "Allocated"
    /\ extent_data' = "Valid"
    /\ alloc_pc' = "Done"
    /\ UNCHANGED <<extent_state, discard_pc>>

FixedDiscardReadList ==
    /\ discard_pc = "Init"
    /\ extent_state = "DiscardPending"
    /\ discard_pc' = "IssueTrim"
    /\ UNCHANGED <<extent_state, extent_data, alloc_pc>>

FixedDiscardTrim ==
    /\ discard_pc = "IssueTrim"
    \* FIX: Discard worker re-verifies extent is still DiscardPending before trimming
    /\ IF extent_state = "DiscardPending" THEN
           /\ extent_data' = "Trimmed"
           /\ extent_state' = "Freed"
       ELSE
           /\ UNCHANGED <<extent_data, extent_state>>
    /\ discard_pc' = "Done"
    /\ UNCHANGED <<alloc_pc>>

\* Discard worker gives up if extent was already reallocated
FixedDiscardSkip ==
    /\ discard_pc = "Init"
    /\ extent_state /= "DiscardPending"
    /\ discard_pc' = "Done"
    /\ UNCHANGED <<extent_state, extent_data, alloc_pc>>

FixedDone ==
    /\ alloc_pc = "Done"
    /\ discard_pc = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedAllocFree
    \/ FixedAllocAllocate
    \/ FixedAllocWrite
    \/ FixedDiscardReadList
    \/ FixedDiscardTrim
    \/ FixedDiscardSkip
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedAllocFree)
    /\ WF_vars(FixedAllocAllocate)
    /\ WF_vars(FixedAllocWrite)
    /\ WF_vars(FixedDiscardReadList)
    /\ WF_vars(FixedDiscardTrim)
    /\ WF_vars(FixedDiscardSkip)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

\* After the allocator finishes writing (alloc_pc = Done), if the extent is
\* Allocated, its data must be Valid (not Trimmed by a concurrent discard).
\* We check this at the end of the alloc cycle to avoid false positives
\* between allocation and write.
NoDataTrimmed ==
    (alloc_pc = "Done" /\ extent_state = "Allocated") => extent_data = "Valid"

(* ===========================================================================
 * Liveness Properties (Track E)
 * =========================================================================== *)

EventualCompletion ==
    <>(alloc_pc = "Done" /\ discard_pc = "Done")

==============================================================================
