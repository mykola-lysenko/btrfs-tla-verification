---------------------- MODULE BtrfsTransactionCommit ----------------------
EXTENDS Integers, FiniteSets

\* The disk state. We model it as a function from block addresses to values.
\* "Nil" represents an unwritten or invalid block.
CONSTANTS MaxTx, NumBlocks

VARIABLES
    disk,           \* disk[addr] = value at that address
    superblock_A,   \* First superblock copy: stores the committed generation
    superblock_B,   \* Second superblock copy
    pending_tx,     \* The transaction currently being committed
    commit_phase,   \* Phase of the commit protocol
    crashed         \* Whether the system has crashed

TypeInvariant ==
    /\ superblock_A \in Nat
    /\ superblock_B \in Nat
    /\ pending_tx \in Nat
    /\ commit_phase \in {"Idle", "WritingData", "WritingRoot",
                         "WritingSB_A", "WritingSB_B", "Committed"}
    /\ crashed \in BOOLEAN

Init ==
    /\ disk = [b \in 1..NumBlocks |-> "Nil"]
    /\ superblock_A = 0
    /\ superblock_B = 0
    /\ pending_tx = 1
    /\ commit_phase = "Idle"
    /\ crashed = FALSE

\* --- Normal Execution Steps ---

BeginCommit ==
    /\ ~crashed
    /\ commit_phase = "Idle"
    /\ pending_tx <= MaxTx
    /\ commit_phase' = "WritingData"
    /\ UNCHANGED <<disk, superblock_A, superblock_B, pending_tx, crashed>>

WriteData ==
    /\ ~crashed
    /\ commit_phase = "WritingData"
    \* COW: write new data to a new block (simplified)
    /\ disk' = [disk EXCEPT ![pending_tx] = pending_tx]
    /\ commit_phase' = "WritingRoot"
    /\ UNCHANGED <<superblock_A, superblock_B, pending_tx, crashed>>

WriteRoot ==
    /\ ~crashed
    /\ commit_phase = "WritingRoot"
    \* Write the new tree root to a new block
    /\ disk' = [disk EXCEPT ![pending_tx + MaxTx] = pending_tx]
    /\ commit_phase' = "WritingSB_A"
    /\ UNCHANGED <<superblock_A, superblock_B, pending_tx, crashed>>

WriteSuperblockA ==
    /\ ~crashed
    /\ commit_phase = "WritingSB_A"
    /\ superblock_A' = pending_tx
    /\ commit_phase' = "WritingSB_B"
    /\ UNCHANGED <<disk, superblock_B, pending_tx, crashed>>

WriteSuperblockB ==
    /\ ~crashed
    /\ commit_phase = "WritingSB_B"
    /\ superblock_B' = pending_tx
    /\ commit_phase' = "Committed"
    /\ UNCHANGED <<disk, superblock_A, pending_tx, crashed>>

AdvanceTx ==
    /\ ~crashed
    /\ commit_phase = "Committed"
    /\ pending_tx' = pending_tx + 1
    /\ commit_phase' = "Idle"
    /\ UNCHANGED <<disk, superblock_A, superblock_B, crashed>>

\* --- Crash and Recovery ---

\* A crash can happen at any point during the commit
Crash ==
    /\ ~crashed
    /\ crashed' = TRUE
    /\ UNCHANGED <<disk, superblock_A, superblock_B, pending_tx, commit_phase>>

\* Recovery: select the superblock with the highest valid generation
\* A superblock is valid if its generation's data and root are on disk
IsValidSuperblock(gen) ==
    /\ gen > 0
    /\ disk[gen] = gen              \* Data block is present
    /\ disk[gen + MaxTx] = gen      \* Root block is present

Recover ==
    /\ crashed
    /\ LET valid_gen == IF IsValidSuperblock(superblock_A) /\ superblock_A >= superblock_B
                        THEN superblock_A
                        ELSE IF IsValidSuperblock(superblock_B)
                             THEN superblock_B
                             ELSE 0
       IN /\ superblock_A' = valid_gen
          /\ superblock_B' = valid_gen
    /\ commit_phase' = "Idle"
    /\ crashed' = FALSE
    /\ UNCHANGED <<disk, pending_tx>>

Next ==
    \/ BeginCommit \/ WriteData \/ WriteRoot
    \/ WriteSuperblockA \/ WriteSuperblockB \/ AdvanceTx
    \/ Crash \/ Recover

\* --- Safety Properties ---

\* After recovery, the active superblock must point to a fully written tree
ConsistencyAfterRecovery ==
    (~crashed /\ commit_phase = "Idle") =>
        LET active_gen == superblock_A
        IN  active_gen = 0 \/
            (disk[active_gen] = active_gen /\ disk[active_gen + MaxTx] = active_gen)

\* The active generation never exceeds the pending transaction
GenerationMonotonicity ==
    superblock_A <= pending_tx /\ superblock_B <= pending_tx

Spec == Init /\ [][Next]_<<disk, superblock_A, superblock_B, pending_tx,
                             commit_phase, crashed>>

==========================================================================
