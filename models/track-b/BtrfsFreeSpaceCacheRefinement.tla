---- MODULE BtrfsFreeSpaceCacheRefinement ----
(*
 * Model: Refinement mapping from Concrete to Abstract Free Space Cache
 *)

EXTENDS BtrfsFreeSpaceCacheConcrete

Abstract == INSTANCE BtrfsFreeSpaceCache WITH
    bg_progress           <- bg_progress,
    bg_last_byte_to_unpin <- bg_last_byte_to_unpin,
    space_cache_count     <- space_cache_added,
    commit_root_switched  <- commit_root_switched,
    tx_a_pc               <- tx_a_state,
    tx_b_pc               <- tx_b_state,
    caching_thread_pc     <- caching_state

Refinement == Abstract!FixedSpec

=============================================================================
