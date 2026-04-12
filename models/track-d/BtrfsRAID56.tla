---------------------------- MODULE BtrfsRAID56 ----------------------------
(*
 * Model: Btrfs RAID56 stripe write hole (partial write / power loss)
 *
 * Bug description:
 * In a RAID5/6 array, a full stripe consists of multiple data blocks and
 * one or more parity blocks. When updating data, Btrfs must write both the
 * new data blocks and the updated parity blocks to disk.
 * The "write hole" occurs if a power loss or crash happens in the middle
 * of these writes. For example, if the data block is written but the parity
 * block is not (or vice versa), the stripe becomes inconsistent.
 * If another drive later fails, the reconstruction using the inconsistent
 * parity will yield corrupt data.
 *
 * Sequence (buggy):
 * 1. Write operation begins updating data and parity.
 * 2. Data block is written to disk.
 * 3. Power loss occurs (system crashes).
 * 4. Recovery reads the stripe. Data block has new data, but parity block
 *    has old parity -> Inconsistent stripe.
 *
 * Fix: Btrfs introduced a journal/intent mechanism (or in ZFS/Btrfs context,
 * write-intent bitmaps or full journal) to track partial writes, allowing
 * recovery to either complete the write or rebuild parity upon next mount.
 *
 * Variables:
 *   disk_data: "Old" | "New"
 *   disk_parity: "Old" | "New"
 *   pc: "Init" | "WriteData" | "WriteParity" | "Done"
 *   power_loss: BOOLEAN
 *   journal: "Empty" | "Intent" | "Done"
 *
 * Invariant: StripeConsistent
 *   If the system is done (or recovered from power loss), the stripe
 *   must be consistent: (disk_data = "Old" /\ disk_parity = "Old") OR
 *                       (disk_data = "New" /\ disk_parity = "New")
 *)

EXTENDS Integers, TLC

VARIABLES
    disk_data,
    disk_parity,
    pc,
    power_loss,
    journal

vars == <<disk_data, disk_parity, pc, power_loss, journal>>

Init ==
    /\ disk_data = "Old"
    /\ disk_parity = "Old"
    /\ pc = "Init"
    /\ power_loss = FALSE
    /\ journal = "Empty"

(* ===========================================================================
 * BUGGY VARIANT: No journal/intent logging, vulnerable to power loss
 * =========================================================================== *)

BuggyWriteData ==
    /\ pc = "Init"
    /\ power_loss = FALSE
    /\ disk_data' = "New"
    /\ pc' = "WriteParity"
    /\ UNCHANGED <<disk_parity, power_loss, journal>>

BuggyWriteParity ==
    /\ pc = "WriteParity"
    /\ power_loss = FALSE
    /\ disk_parity' = "New"
    /\ pc' = "Done"
    /\ UNCHANGED <<disk_data, power_loss, journal>>

BuggyPowerLoss ==
    /\ power_loss = FALSE
    /\ pc \in {"WriteParity", "Done"}  \* Can happen after data write or at end
    /\ power_loss' = TRUE
    /\ pc' = "Done"  \* System halts
    /\ UNCHANGED <<disk_data, disk_parity, journal>>

BuggyDone ==
    /\ pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyWriteData
    \/ BuggyWriteParity
    \/ BuggyPowerLoss
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyWriteData)
    /\ WF_vars(BuggyWriteParity)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Uses write-intent journal to recover from partial writes
 * =========================================================================== *)

FixedWriteIntent ==
    /\ pc = "Init"
    /\ power_loss = FALSE
    /\ journal' = "Intent"
    /\ pc' = "WriteData"
    /\ UNCHANGED <<disk_data, disk_parity, power_loss>>

FixedWriteData ==
    /\ pc = "WriteData"
    /\ power_loss = FALSE
    /\ disk_data' = "New"
    /\ pc' = "WriteParity"
    /\ UNCHANGED <<disk_parity, power_loss, journal>>

FixedWriteParity ==
    /\ pc = "WriteParity"
    /\ power_loss = FALSE
    /\ disk_parity' = "New"
    /\ pc' = "ClearIntent"
    /\ UNCHANGED <<disk_data, power_loss, journal>>

FixedClearIntent ==
    /\ pc = "ClearIntent"
    /\ power_loss = FALSE
    /\ journal' = "Done"
    /\ pc' = "Done"
    /\ UNCHANGED <<disk_data, disk_parity, power_loss>>

FixedPowerLoss ==
    /\ power_loss = FALSE
    /\ pc \in {"WriteData", "WriteParity", "ClearIntent"}
    /\ power_loss' = TRUE
    /\ pc' = "Recover"  \* System halts, next state is recovery on mount
    /\ UNCHANGED <<disk_data, disk_parity, journal>>

FixedRecover ==
    /\ pc = "Recover"
    /\ power_loss = TRUE
    \* On mount, if journal shows Intent, we must rebuild parity to match data
    \* (or rollback, but Btrfs rebuilds parity from data blocks).
    /\ IF journal = "Intent" THEN
           /\ disk_parity' = disk_data  \* Rebuild parity to match data
           /\ journal' = "Done"
       ELSE
           /\ UNCHANGED <<disk_parity, journal>>
    /\ pc' = "Done"
    /\ UNCHANGED <<disk_data, power_loss>>

FixedDone ==
    /\ pc = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedWriteIntent
    \/ FixedWriteData
    \/ FixedWriteParity
    \/ FixedClearIntent
    \/ FixedPowerLoss
    \/ FixedRecover
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedWriteIntent)
    /\ WF_vars(FixedWriteData)
    /\ WF_vars(FixedWriteParity)
    /\ WF_vars(FixedClearIntent)
    /\ WF_vars(FixedRecover)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

\* If the system is done (normal completion or post-recovery), the stripe must
\* be consistent. It can't have "New" data but "Old" parity, or vice versa.
StripeConsistent ==
    pc = "Done" => (disk_data = disk_parity)

(* ===========================================================================
 * Liveness Properties (Track E)
 * =========================================================================== *)

\* The system must eventually reach the Done state, either through normal
\* completion or through recovery after a power loss.
EventualCompletion ==
    <>(pc = "Done")

==============================================================================
