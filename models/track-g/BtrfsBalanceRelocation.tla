---- MODULE BtrfsBalanceRelocation ----
(*
 * Model: Btrfs Balance / Relocation Race
 *
 * Bug description:
 * When Btrfs balances (relocates) a block group, it copies extents from the
 * old block group to a new one. Concurrently, user writes might be modifying
 * those same extents. If a write goes to the old block group after it has
 * been copied but before the relocation finishes, the write is lost.
 *
 * Fix: Relocation marks the block group as Read-Only (RO) before copying.
 * Any concurrent writes are forced to allocate from a different block group.
 *)

EXTENDS Integers, TLC

VARIABLES
    block_group_ro,   \* BOOLEAN
    extent_copied,    \* BOOLEAN
    user_write_done,  \* BOOLEAN
    write_target,     \* "None" | "OldBG" | "NewBG"
    reloc_state,
    write_state,
    write_after_copy_started

vars == <<block_group_ro, extent_copied, user_write_done, write_target, reloc_state, write_state, write_after_copy_started>>

Init ==
    /\ block_group_ro = FALSE
    /\ extent_copied = FALSE
    /\ user_write_done = FALSE
    /\ write_target = "None"
    /\ reloc_state = "Init"
    /\ write_state = "Init"
    /\ write_after_copy_started = FALSE

(* ===========================================================================
 * BUGGY VARIANT: Relocation copies without setting RO first
 * =========================================================================== *)

BuggyRelocCopy ==
    /\ reloc_state = "Init"
    /\ extent_copied' = TRUE
    /\ reloc_state' = "Done"
    /\ UNCHANGED <<block_group_ro, user_write_done, write_target, write_state, write_after_copy_started>>

BuggyUserWrite ==
    /\ write_state = "Init"
    /\ write_target' = "OldBG"
    /\ user_write_done' = TRUE
    /\ write_after_copy_started' = (reloc_state = "Done")
    /\ write_state' = "Done"
    /\ UNCHANGED <<block_group_ro, extent_copied, reloc_state>>

BuggyDone ==
    /\ reloc_state = "Done"
    /\ write_state = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyRelocCopy
    \/ BuggyUserWrite
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyRelocCopy)
    /\ WF_vars(BuggyUserWrite)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Relocation sets RO before copying
 * =========================================================================== *)

FixedRelocSetRO ==
    /\ reloc_state = "Init"
    /\ block_group_ro' = TRUE
    /\ reloc_state' = "Copy"
    /\ UNCHANGED <<extent_copied, user_write_done, write_target, write_state, write_after_copy_started>>

FixedRelocCopy ==
    /\ reloc_state = "Copy"
    /\ extent_copied' = TRUE
    /\ reloc_state' = "Done"
    /\ UNCHANGED <<block_group_ro, user_write_done, write_target, write_state, write_after_copy_started>>

FixedUserWrite ==
    /\ write_state = "Init"
    /\ write_target' = IF block_group_ro THEN "NewBG" ELSE "OldBG"
    /\ user_write_done' = TRUE
    /\ write_after_copy_started' = (reloc_state \in {"Copy", "Done"})
    /\ write_state' = "Done"
    /\ UNCHANGED <<block_group_ro, extent_copied, reloc_state>>

FixedDone ==
    /\ reloc_state = "Done"
    /\ write_state = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedRelocSetRO
    \/ FixedRelocCopy
    \/ FixedUserWrite
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedRelocSetRO)
    /\ WF_vars(FixedRelocCopy)
    /\ WF_vars(FixedUserWrite)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

\* The real bug is when write happens AFTER copy starts but BEFORE it finishes.
\* If write happens BEFORE copy starts (write_state="Done" then reloc starts), the copy WILL include the new data.
\* The bug is when write_target = "OldBG" and extent_copied = TRUE
\* BUT the write happened AFTER the copy started (meaning the copy missed the write).
\* We need a ghost variable to track if write happened after copy.
NoLostWrite ==
    (reloc_state = "Done" /\ write_state = "Done") =>
        ~(write_target = "OldBG" /\ extent_copied = TRUE /\ write_after_copy_started = TRUE)

EventualCompletion ==
    <>(reloc_state = "Done" /\ write_state = "Done")

=============================================================================
