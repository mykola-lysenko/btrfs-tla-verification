---------------------------- MODULE BtrfsDevReplace ----------------------------
(*
 * Model: Btrfs concurrent read/write race during device replace
 *
 * Bug description:
 * During a device replace operation, Btrfs copies data from the source device
 * to the target device. A race condition occurs if a concurrent write operation
 * modifies data on the source device while it is being copied. If the write
 * happens after the copy reads the old data but before the copy writes to the
 * target device, the target device will receive stale data. When the replace
 * finishes, the target device will have corrupted/stale data.
 *
 * Sequence (buggy):
 * 1. Replace thread reads data from source (data = "Old").
 * 2. Concurrent Write thread writes "New" to source and target.
 *    (Actually, during replace, writes go to BOTH devices).
 * 3. Replace thread writes the data it read ("Old") to the target.
 * 4. Result: Source has "New", Target has "Old" -> Inconsistent.
 *
 * Fix: Btrfs uses a synchronization mechanism (like a lock or a sequence counter)
 * to ensure that if a write happens concurrently with a replace copy, the replace
 * copy either waits for the write, or the write waits for the copy, OR the
 * replace copy is aborted/retried for that extent.
 * Here we model a simple lock per extent.
 *
 * Variables:
 *   src_data: "Old" | "New"
 *   tgt_data: "Empty" | "Old" | "New"
 *   replace_read_data: "Empty" | "Old" | "New"
 *   replace_pc: "Init" | "ReadSrc" | "WriteTgt" | "Done"
 *   write_pc: "Init" | "WriteBoth" | "Done"
 *   extent_lock: "Free" | "Replace" | "Write"
 *
 * Invariant: DataConsistent (src_data = tgt_data when both done)
 *)

EXTENDS Integers, TLC

VARIABLES
    src_data,
    tgt_data,
    replace_read_data,
    replace_pc,
    write_pc,
    extent_lock

vars == <<src_data, tgt_data, replace_read_data, replace_pc, write_pc, extent_lock>>

Init ==
    /\ src_data = "Old"
    /\ tgt_data = "Empty"
    /\ replace_read_data = "Empty"
    /\ replace_pc = "Init"
    /\ write_pc = "Init"
    /\ extent_lock = "Free"

(* ===========================================================================
 * BUGGY VARIANT: No synchronization between replace and write
 * =========================================================================== *)

BuggyReplaceRead ==
    /\ replace_pc = "Init"
    /\ replace_read_data' = src_data
    /\ replace_pc' = "WriteTgt"
    /\ UNCHANGED <<src_data, tgt_data, write_pc, extent_lock>>

BuggyReplaceWrite ==
    /\ replace_pc = "WriteTgt"
    /\ tgt_data' = replace_read_data
    /\ replace_pc' = "Done"
    /\ UNCHANGED <<src_data, replace_read_data, write_pc, extent_lock>>

BuggyWriteBoth ==
    /\ write_pc = "Init"
    /\ src_data' = "New"
    /\ tgt_data' = "New"
    /\ write_pc' = "Done"
    /\ UNCHANGED <<replace_read_data, replace_pc, extent_lock>>

BuggyDone ==
    /\ replace_pc = "Done"
    /\ write_pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyReplaceRead
    \/ BuggyReplaceWrite
    \/ BuggyWriteBoth
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyReplaceRead)
    /\ WF_vars(BuggyReplaceWrite)
    /\ WF_vars(BuggyWriteBoth)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Replace and Write synchronize using extent_lock
 * =========================================================================== *)

FixedReplaceLockAndRead ==
    /\ replace_pc = "Init"
    /\ extent_lock = "Free"
    /\ extent_lock' = "Replace"
    /\ replace_read_data' = src_data
    /\ replace_pc' = "WriteTgt"
    /\ UNCHANGED <<src_data, tgt_data, write_pc>>

FixedReplaceWriteAndUnlock ==
    /\ replace_pc = "WriteTgt"
    /\ tgt_data' = replace_read_data
    /\ extent_lock' = "Free"
    /\ replace_pc' = "Done"
    /\ UNCHANGED <<src_data, replace_read_data, write_pc>>

FixedWriteLockAndWrite ==
    /\ write_pc = "Init"
    /\ extent_lock = "Free"
    /\ extent_lock' = "Write"
    /\ src_data' = "New"
    /\ tgt_data' = "New"
    /\ write_pc' = "Unlock"
    /\ UNCHANGED <<replace_read_data, replace_pc>>

FixedWriteUnlock ==
    /\ write_pc = "Unlock"
    /\ extent_lock' = "Free"
    /\ write_pc' = "Done"
    /\ UNCHANGED <<src_data, tgt_data, replace_read_data, replace_pc>>

FixedDone ==
    /\ replace_pc = "Done"
    /\ write_pc = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedReplaceLockAndRead
    \/ FixedReplaceWriteAndUnlock
    \/ FixedWriteLockAndWrite
    \/ FixedWriteUnlock
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedReplaceLockAndRead)
    /\ WF_vars(FixedReplaceWriteAndUnlock)
    /\ WF_vars(FixedWriteLockAndWrite)
    /\ WF_vars(FixedWriteUnlock)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

\* When both operations are complete, the target device must match the source device.
DataConsistent ==
    (replace_pc = "Done" /\ write_pc = "Done") =>
        (src_data = tgt_data)

(* ===========================================================================
 * Liveness Properties (Track E)
 * =========================================================================== *)

EventualCompletion ==
    <>(replace_pc = "Done" /\ write_pc = "Done")

==============================================================================
