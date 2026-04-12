---------------------------- MODULE BtrfsCOWPath ----------------------------
(*
 * Model: Btrfs COW path and btrfs_search_slot UAF (CVE-2023-1611)
 *
 * Real code: fs/btrfs/ctree.c, fs/btrfs/extent_io.c
 *
 * Bug description:
 * A use-after-free flaw exists in btrfs_search_slot. When traversing the B-tree,
 * a reader thread can retain a pointer to an extent buffer (node) that is concurrently
 * being CoW'd (Copy-On-Write) by a writer thread. If the writer frees the original
 * node and the reader accesses it without proper reference counting, it triggers a UAF.
 *
 * Sequence (buggy):
 * 1. Reader calls btrfs_search_slot, gets a pointer to node N (no refcount bump).
 * 2. Writer CoWs node N: allocates N', copies data, updates parent, drops ref on N.
 * 3. Node N's refcount reaches 0 -> freed.
 * 4. Reader accesses N -> UAF.
 *
 * Fix: Reader must call get_extent_buffer() to bump the refcount before using N.
 *      Writer's free_extent_buffer() only frees when refcount reaches 0.
 *      This ensures the node cannot be freed while the reader holds a reference.
 *
 * Variables:
 *   node_refcount: integer (0 = freed, 1 = initial, 2+ = held by readers)
 *   node_state: "Valid" | "Freed"
 *   reader_pc: "Init" | "ReadData" | "PutRef" | "Done"
 *   writer_pc: "Init" | "FreeNode" | "Done"
 *   reader_has_ptr: TRUE | FALSE (reader obtained a pointer to node N)
 *   crash_uaf: TRUE | FALSE
 *
 * Invariant: NoUAF
 *)

EXTENDS Integers, TLC

VARIABLES
    node_refcount,
    node_state,
    reader_pc,
    writer_pc,
    reader_has_ptr,
    crash_uaf

vars == <<node_refcount, node_state, reader_pc, writer_pc, reader_has_ptr, crash_uaf>>

Init ==
    /\ node_refcount = 1
    /\ node_state = "Valid"
    /\ reader_pc = "Init"
    /\ writer_pc = "Init"
    /\ reader_has_ptr = FALSE
    /\ crash_uaf = FALSE

(* ===========================================================================
 * BUGGY VARIANT: Reader does not bump refcount before using pointer
 * =========================================================================== *)

\* Reader gets a pointer to N (no refcount bump) -- can happen any time
BuggyReaderGetPointer ==
    /\ reader_pc = "Init"
    /\ reader_has_ptr' = TRUE
    /\ reader_pc' = "ReadData"
    /\ UNCHANGED <<node_refcount, node_state, writer_pc, crash_uaf>>

\* Reader accesses the node -- UAF if node was freed
BuggyReaderReadData ==
    /\ reader_pc = "ReadData"
    /\ crash_uaf' = IF node_state = "Freed" THEN TRUE ELSE crash_uaf
    /\ reader_pc' = "Done"
    /\ UNCHANGED <<node_refcount, node_state, writer_pc, reader_has_ptr>>

\* Writer starts CoW
BuggyWriterCoW ==
    /\ writer_pc = "Init"
    /\ writer_pc' = "FreeNode"
    /\ UNCHANGED <<node_refcount, node_state, reader_pc, reader_has_ptr, crash_uaf>>

\* Writer drops its reference to the original node
BuggyWriterFreeNode ==
    /\ writer_pc = "FreeNode"
    /\ node_refcount' = node_refcount - 1
    /\ node_state' = IF node_refcount - 1 = 0 THEN "Freed" ELSE node_state
    /\ writer_pc' = "Done"
    /\ UNCHANGED <<reader_pc, reader_has_ptr, crash_uaf>>

BuggyDone ==
    /\ reader_pc = "Done"
    /\ writer_pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyReaderGetPointer
    \/ BuggyReaderReadData
    \/ BuggyWriterCoW
    \/ BuggyWriterFreeNode
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyReaderGetPointer)
    /\ WF_vars(BuggyReaderReadData)
    /\ WF_vars(BuggyWriterCoW)
    /\ WF_vars(BuggyWriterFreeNode)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Reader bumps refcount (get_extent_buffer) before using pointer
 * =========================================================================== *)

\* Reader gets a pointer AND bumps refcount atomically
FixedReaderGetRef ==
    /\ reader_pc = "Init"
    /\ node_state = "Valid"   \* can only get ref if node is still valid
    /\ node_refcount' = node_refcount + 1
    /\ reader_has_ptr' = TRUE
    /\ reader_pc' = "ReadData"
    /\ UNCHANGED <<node_state, writer_pc, crash_uaf>>

\* Reader accesses the node (refcount > 0 guarantees it's valid)
FixedReaderReadData ==
    /\ reader_pc = "ReadData"
    /\ crash_uaf' = IF node_state = "Freed" THEN TRUE ELSE crash_uaf
    /\ reader_pc' = "PutRef"
    /\ UNCHANGED <<node_refcount, node_state, writer_pc, reader_has_ptr>>

\* Reader drops its reference
FixedReaderPutRef ==
    /\ reader_pc = "PutRef"
    /\ node_refcount' = node_refcount - 1
    /\ node_state' = IF node_refcount - 1 = 0 THEN "Freed" ELSE node_state
    /\ reader_pc' = "Done"
    /\ UNCHANGED <<writer_pc, reader_has_ptr, crash_uaf>>

\* Writer starts CoW
FixedWriterCoW ==
    /\ writer_pc = "Init"
    /\ writer_pc' = "FreeNode"
    /\ UNCHANGED <<node_refcount, node_state, reader_pc, reader_has_ptr, crash_uaf>>

\* Writer drops its reference
FixedWriterFreeNode ==
    /\ writer_pc = "FreeNode"
    /\ node_refcount' = node_refcount - 1
    /\ node_state' = IF node_refcount - 1 = 0 THEN "Freed" ELSE node_state
    /\ writer_pc' = "Done"
    /\ UNCHANGED <<reader_pc, reader_has_ptr, crash_uaf>>

FixedDone ==
    /\ reader_pc = "Done"
    /\ writer_pc = "Done"
    /\ UNCHANGED vars

\* Reader gives up if node was freed before it could get a reference (returns -EAGAIN)
FixedReaderSkip ==
    /\ reader_pc = "Init"
    /\ node_state = "Freed"
    /\ reader_pc' = "Done"
    /\ UNCHANGED <<node_refcount, node_state, writer_pc, reader_has_ptr, crash_uaf>>

FixedNext ==
    \/ FixedReaderGetRef
    \/ FixedReaderReadData
    \/ FixedReaderPutRef
    \/ FixedWriterCoW
    \/ FixedWriterFreeNode
    \/ FixedReaderSkip
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedReaderGetRef)
    /\ WF_vars(FixedReaderReadData)
    /\ WF_vars(FixedReaderPutRef)
    /\ WF_vars(FixedWriterCoW)
    /\ WF_vars(FixedWriterFreeNode)
    /\ WF_vars(FixedReaderSkip)  \* Reader must eventually give up if node is freed

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

NoUAF ==
    crash_uaf = FALSE

RefcountNonNegative ==
    node_refcount >= 0

\* If reader is in ReadData state, node must still be valid (refcount > 0)
ReadDataImpliesValid ==
    reader_pc = "ReadData" => node_state = "Valid"

(* ===========================================================================
 * Liveness Properties (Track E)
 * =========================================================================== *)

\* Both the reader and writer must eventually finish their work.
\* This proves that the refcounting mechanism doesn't introduce a deadlock
\* or starvation for either thread.
EventualCompletion ==
    <>(reader_pc = "Done" /\ writer_pc = "Done")

==============================================================================
