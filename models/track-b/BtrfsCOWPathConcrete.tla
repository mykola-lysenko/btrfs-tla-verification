---- MODULE BtrfsCOWPathConcrete ----
(*
 * Model: Concrete Btrfs COW Path
 *
 * This model is a detailed representation of fs/btrfs/ctree.c btrfs_search_slot
 * and btrfs_cow_block. It models the actual reference counting mechanism.
 *)

EXTENDS Integers, TLC

VARIABLES
    \* Concrete node state
    node_refs,       \* atomic_t refs
    node_is_freed,   \* BOOLEAN

    \* Thread states
    reader_state,
    writer_state,
    reader_ptr,      \* BOOLEAN
    crash_occurred

vars == <<node_refs, node_is_freed, reader_state, writer_state, reader_ptr, crash_occurred>>

Init ==
    /\ node_refs = 1
    /\ node_is_freed = FALSE
    /\ reader_state = "Init"
    /\ writer_state = "Init"
    /\ reader_ptr = FALSE
    /\ crash_occurred = FALSE

\* btrfs_search_slot: get_extent_buffer
ReaderGetRef ==
    /\ reader_state = "Init"
    /\ node_is_freed = FALSE
    /\ node_refs' = node_refs + 1
    /\ reader_ptr' = TRUE
    /\ reader_state' = "ReadData"
    /\ UNCHANGED <<node_is_freed, writer_state, crash_occurred>>

\* btrfs_search_slot: read node
ReaderReadData ==
    /\ reader_state = "ReadData"
    /\ crash_occurred' = IF node_is_freed THEN TRUE ELSE crash_occurred
    /\ reader_state' = "PutRef"
    /\ UNCHANGED <<node_refs, node_is_freed, writer_state, reader_ptr>>

\* free_extent_buffer (reader side)
ReaderPutRef ==
    /\ reader_state = "PutRef"
    /\ node_refs' = node_refs - 1
    /\ node_is_freed' = IF node_refs - 1 = 0 THEN TRUE ELSE node_is_freed
    /\ reader_state' = "Done"
    /\ UNCHANGED <<writer_state, reader_ptr, crash_occurred>>

\* btrfs_cow_block
WriterCoW ==
    /\ writer_state = "Init"
    /\ writer_state' = "FreeNode"
    /\ UNCHANGED <<node_refs, node_is_freed, reader_state, reader_ptr, crash_occurred>>

\* free_extent_buffer (writer side)
WriterFreeNode ==
    /\ writer_state = "FreeNode"
    /\ node_refs' = node_refs - 1
    /\ node_is_freed' = IF node_refs - 1 = 0 THEN TRUE ELSE node_is_freed
    /\ writer_state' = "Done"
    /\ UNCHANGED <<reader_state, reader_ptr, crash_occurred>>

ReaderSkip ==
    /\ reader_state = "Init"
    /\ node_is_freed = TRUE
    /\ reader_state' = "Done"
    /\ UNCHANGED <<node_refs, node_is_freed, writer_state, reader_ptr, crash_occurred>>

Done ==
    /\ reader_state = "Done"
    /\ writer_state = "Done"
    /\ UNCHANGED vars

Next ==
    \/ ReaderGetRef
    \/ ReaderReadData
    \/ ReaderPutRef
    \/ WriterCoW
    \/ WriterFreeNode
    \/ ReaderSkip
    \/ Done

Fairness ==
    /\ WF_vars(ReaderGetRef)
    /\ WF_vars(ReaderReadData)
    /\ WF_vars(ReaderPutRef)
    /\ WF_vars(WriterCoW)
    /\ WF_vars(WriterFreeNode)
    /\ WF_vars(ReaderSkip)

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
