---------------------------- MODULE BtrfsScrub ----------------------------
(*
 * Model: Btrfs concurrent scrub and write to same block group race
 *
 * Bug description:
 * Btrfs scrub verifies data integrity by reading all blocks and checking
 * checksums. If it finds a bad block, it attempts to rewrite it from a good
 * copy (e.g., in a RAID setup).
 * A race condition occurs if a concurrent user write modifies a block
 * AFTER scrub has read it and decided to repair it, but BEFORE scrub
 * actually writes the repair. Scrub might overwrite the user's new data
 * with the old "good" data, effectively discarding the user write.
 *
 * Sequence (buggy):
 * 1. Scrub reads block data ("Old"), decides to repair.
 * 2. User writes new data to block ("New").
 * 3. Scrub writes repair ("Old") to block.
 * 4. Result: Block has "Old" data, user expected "New" -> Data loss.
 *
 * Fix: Btrfs marks the block group as read-only (RO) during scrub so that
 * concurrent writes must wait. This ensures scrub's repair cannot overwrite
 * a write that happened after scrub started.
 *
 * Variables:
 *   bg_state: "RW" | "RO"
 *   block_data: "Old" | "New"
 *   scrub_read_data: "None" | "Old" | "New"
 *   scrub_pc: "Init" | "Read" | "Repair" | "Done"
 *   write_pc: "Init" | "Write" | "Done"
 *
 * Invariant: NoLostWrite
 *   If write is Done and scrub is Done, block_data must be "New".
 *)

EXTENDS Integers, TLC

VARIABLES
    bg_state,
    block_data,
    scrub_read_data,
    scrub_pc,
    write_pc

vars == <<bg_state, block_data, scrub_read_data, scrub_pc, write_pc>>

Init ==
    /\ bg_state = "RW"
    /\ block_data = "Old"
    /\ scrub_read_data = "None"
    /\ scrub_pc = "Init"
    /\ write_pc = "Init"

(* ===========================================================================
 * BUGGY VARIANT: No synchronization between scrub and write
 * =========================================================================== *)

BuggyScrubRead ==
    /\ scrub_pc = "Init"
    /\ scrub_read_data' = block_data  \* Read current block data
    /\ scrub_pc' = "Repair"
    /\ UNCHANGED <<bg_state, block_data, write_pc>>

BuggyScrubRepair ==
    /\ scrub_pc = "Repair"
    \* BUG: Unconditionally writes the data it read, even if block was updated
    /\ block_data' = scrub_read_data
    /\ scrub_pc' = "Done"
    /\ UNCHANGED <<bg_state, scrub_read_data, write_pc>>

BuggyWrite ==
    /\ write_pc = "Init"
    /\ block_data' = "New"
    /\ write_pc' = "Done"
    /\ UNCHANGED <<bg_state, scrub_read_data, scrub_pc>>

BuggyDone ==
    /\ scrub_pc = "Done"
    /\ write_pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyScrubRead
    \/ BuggyScrubRepair
    \/ BuggyWrite
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyScrubRead)
    /\ WF_vars(BuggyScrubRepair)
    /\ WF_vars(BuggyWrite)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Scrub marks Block Group as RO during its read-repair cycle
 * =========================================================================== *)

FixedScrubMarkROAndRead ==
    /\ scrub_pc = "Init"
    /\ bg_state = "RW"
    /\ bg_state' = "RO"
    /\ scrub_read_data' = block_data  \* Read under RO lock
    /\ scrub_pc' = "Repair"
    /\ UNCHANGED <<block_data, write_pc>>

FixedScrubRepairAndUnlock ==
    /\ scrub_pc = "Repair"
    \* FIX: Repair writes the data it read. Since BG was RO during read,
    \* no concurrent write could have changed block_data between read and repair.
    /\ block_data' = scrub_read_data
    /\ bg_state' = "RW"
    /\ scrub_pc' = "Done"
    /\ UNCHANGED <<scrub_read_data, write_pc>>

FixedWrite ==
    /\ write_pc = "Init"
    /\ bg_state = "RW"  \* FIX: Writer must wait if BG is RO
    /\ block_data' = "New"
    /\ write_pc' = "Done"
    /\ UNCHANGED <<bg_state, scrub_read_data, scrub_pc>>

FixedDone ==
    /\ scrub_pc = "Done"
    /\ write_pc = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedScrubMarkROAndRead
    \/ FixedScrubRepairAndUnlock
    \/ FixedWrite
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedScrubMarkROAndRead)
    /\ WF_vars(FixedScrubRepairAndUnlock)
    /\ WF_vars(FixedWrite)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

\* When both operations are done, the block must have the most recent write.
\* If the write completed, its data ("New") must be preserved.
NoLostWrite ==
    (write_pc = "Done" /\ scrub_pc = "Done") => block_data = "New"

(* ===========================================================================
 * Liveness Properties (Track E)
 * =========================================================================== *)

\* Both the scrub and write operations eventually complete.
\* This proves that the RO lock does not cause a deadlock or starvation
\* for either the scrub worker or the user writer.
EventualCompletion ==
    <>(scrub_pc = "Done" /\ write_pc = "Done")

==============================================================================
