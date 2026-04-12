---- MODULE BtrfsAutodefrag ----
(*
 * Model: Btrfs Autodefrag vs. User Write Race
 *
 * Bug description:
 * The autodefrag worker thread scans for fragmented files and defragments
 * them by copying their extents to a contiguous location. Concurrently,
 * a user process might be writing new data to the same file.
 * If autodefrag reads the old data, the user writes new data, and then
 * autodefrag overwrites the file with the old data it read, the user write
 * is silently lost.
 *
 * Fix: Autodefrag must hold the inode lock while reading and writing the
 * defragmented extents, ensuring user writes are blocked during the process.
 *)

EXTENDS Integers, TLC

VARIABLES
    inode_data,       \* "Fragmented" | "NewData" | "Defragged"
    inode_lock,       \* "Free" | "User" | "Defrag"
    defrag_read_data, \* "None" | "Fragmented" | "NewData"
    user_state,
    defrag_state

vars == <<inode_data, inode_lock, defrag_read_data, user_state, defrag_state>>

Init ==
    /\ inode_data = "Fragmented"
    /\ inode_lock = "Free"
    /\ defrag_read_data = "None"
    /\ user_state = "Init"
    /\ defrag_state = "Init"

(* ===========================================================================
 * BUGGY VARIANT: Autodefrag without inode lock
 * =========================================================================== *)

BuggyUserWrite ==
    /\ user_state = "Init"
    /\ inode_lock = "Free"
    /\ inode_data' = "NewData"
    /\ user_state' = "Done"
    /\ UNCHANGED <<inode_lock, defrag_read_data, defrag_state>>

BuggyDefragRead ==
    /\ defrag_state = "Init"
    /\ defrag_read_data' = inode_data
    /\ defrag_state' = "Write"
    /\ UNCHANGED <<inode_data, inode_lock, user_state>>

BuggyDefragWrite ==
    /\ defrag_state = "Write"
    /\ inode_data' = "Defragged"  \* Overwrites with whatever it read (conceptually)
    /\ defrag_state' = "Done"
    /\ UNCHANGED <<inode_lock, defrag_read_data, user_state>>

BuggyDone ==
    /\ user_state = "Done"
    /\ defrag_state = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyUserWrite
    \/ BuggyDefragRead
    \/ BuggyDefragWrite
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyUserWrite)
    /\ WF_vars(BuggyDefragRead)
    /\ WF_vars(BuggyDefragWrite)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Autodefrag holds inode lock
 * =========================================================================== *)

FixedUserWrite ==
    /\ user_state = "Init"
    /\ inode_lock = "Free"
    /\ inode_data' = "NewData"
    /\ user_state' = "Done"
    /\ UNCHANGED <<inode_lock, defrag_read_data, defrag_state>>

FixedDefragLockAndRead ==
    /\ defrag_state = "Init"
    /\ inode_lock = "Free"
    /\ inode_lock' = "Defrag"
    /\ defrag_read_data' = inode_data
    /\ defrag_state' = "Write"
    /\ UNCHANGED <<inode_data, user_state>>

FixedDefragWriteAndUnlock ==
    /\ defrag_state = "Write"
    /\ inode_data' = "Defragged"
    /\ inode_lock' = "Free"
    /\ defrag_state' = "Done"
    /\ UNCHANGED <<defrag_read_data, user_state>>

FixedDone ==
    /\ user_state = "Done"
    /\ defrag_state = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedUserWrite
    \/ FixedDefragLockAndRead
    \/ FixedDefragWriteAndUnlock
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedUserWrite)
    /\ WF_vars(FixedDefragLockAndRead)
    /\ WF_vars(FixedDefragWriteAndUnlock)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

\* If the user wrote new data, it shouldn't be overwritten by an old defrag.
\* In reality, if defrag runs AFTER user write, it defrags the new data.
\* If user write runs AFTER defrag, the new data is preserved.
\* The bug is when defrag reads, then user writes, then defrag writes.
\* In that case, defrag_read_data = "Fragmented", user_state = "Done",
\* and defrag overwrites with "Defragged".
NoLostWrite ==
    (user_state = "Done" /\ defrag_state = "Done") =>
        ~(defrag_read_data = "Fragmented" /\ inode_data = "Defragged")

EventualCompletion ==
    <>(user_state = "Done" /\ defrag_state = "Done")

=============================================================================
