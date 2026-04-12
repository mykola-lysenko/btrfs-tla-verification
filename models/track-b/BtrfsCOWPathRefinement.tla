---- MODULE BtrfsCOWPathRefinement ----
(*
 * Model: Refinement mapping from Concrete to Abstract COW Path
 *)

EXTENDS BtrfsCOWPathConcrete

\* Map the concrete node_is_freed BOOLEAN to the abstract node_state STRING
AbstractNodeState ==
    IF node_is_freed THEN "Freed" ELSE "Valid"

Abstract == INSTANCE BtrfsCOWPath WITH
    node_refcount  <- node_refs,
    node_state     <- AbstractNodeState,
    reader_pc      <- reader_state,
    writer_pc      <- writer_state,
    reader_has_ptr <- reader_ptr,
    crash_uaf      <- crash_occurred

Refinement == Abstract!FixedSpec

=============================================================================
