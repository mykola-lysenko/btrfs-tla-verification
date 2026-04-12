---- MODULE BtrfsFreeSpaceCacheConcrete ----
(*
 * Model: Concrete Btrfs Free Space Cache
 *
 * This model is a detailed representation of fs/btrfs/free-space-cache.c
 * btrfs_cache_block_group, switch_commit_roots, and unpin_extent_range.
 *)

EXTENDS Integers, TLC

VARIABLES
    \* Concrete variables from struct btrfs_block_group
    bg_progress,            \* u64 progress
    bg_last_byte_to_unpin,  \* u64 last_byte_to_unpin
    bg_cached,              \* enum btrfs_block_group_cache_state
    
    \* System state
    commit_root_switched,   \* BOOLEAN
    space_cache_added,      \* INT (number of times added)
    
    \* Thread states
    tx_a_state,
    tx_b_state,
    caching_state

vars == <<bg_progress, bg_last_byte_to_unpin, bg_cached, commit_root_switched,
          space_cache_added, tx_a_state, tx_b_state, caching_state>>

Init ==
    /\ bg_progress = 0
    /\ bg_last_byte_to_unpin = 0
    /\ bg_cached = "BTRFS_CACHE_NO"
    /\ commit_root_switched = FALSE
    /\ space_cache_added = 0
    /\ tx_a_state = "Init"
    /\ tx_b_state = "Init"
    /\ caching_state = "Init"

\* Tx A: delete extent, start caching synchronously
TxADelete ==
    /\ tx_a_state = "Init"
    /\ caching_state' = "Cache"
    /\ tx_a_state' = "WaitCache"
    /\ bg_cached' = "BTRFS_CACHE_STARTED"
    /\ UNCHANGED <<bg_progress, bg_last_byte_to_unpin, commit_root_switched, space_cache_added, tx_b_state>>

\* Caching thread (btrfs_cache_block_group)
CachingThread ==
    /\ caching_state = "Cache"
    /\ commit_root_switched = FALSE
    /\ bg_progress' = 1
    /\ bg_cached' = "BTRFS_CACHE_FINISHED"
    /\ caching_state' = "Done"
    /\ UNCHANGED <<bg_last_byte_to_unpin, commit_root_switched, space_cache_added, tx_a_state, tx_b_state>>

\* Tx A: wait for caching to finish
TxAWaitDone ==
    /\ tx_a_state = "WaitCache"
    /\ caching_state = "Done"
    /\ tx_a_state' = "SwitchRoots"
    /\ UNCHANGED <<bg_progress, bg_last_byte_to_unpin, bg_cached, commit_root_switched, space_cache_added, tx_b_state, caching_state>>

\* Tx A: switch_commit_roots
TxASwitchRoots ==
    /\ tx_a_state = "SwitchRoots"
    /\ bg_last_byte_to_unpin' = bg_progress
    /\ commit_root_switched' = TRUE
    /\ tx_a_state' = "SuperCommitted"
    /\ UNCHANGED <<bg_progress, bg_cached, space_cache_added, tx_b_state, caching_state>>

\* Tx B: switch_commit_roots
TxBSwitchRoots ==
    /\ tx_b_state = "Init"
    /\ tx_a_state \in {"SuperCommitted", "Done"}
    /\ bg_last_byte_to_unpin' = bg_progress
    /\ tx_b_state' = "Done"
    /\ UNCHANGED <<bg_progress, bg_cached, commit_root_switched, space_cache_added, tx_a_state, caching_state>>

\* Tx A: unpin_extent_range
TxAUnpin ==
    /\ tx_a_state = "SuperCommitted"
    /\ space_cache_added' = IF bg_last_byte_to_unpin = 1 THEN space_cache_added + 1 ELSE space_cache_added
    /\ tx_a_state' = "Done"
    /\ UNCHANGED <<bg_progress, bg_last_byte_to_unpin, bg_cached, commit_root_switched, tx_b_state, caching_state>>

Done ==
    /\ tx_a_state = "Done"
    /\ tx_b_state = "Done"
    /\ caching_state = "Done"
    /\ UNCHANGED vars

Next ==
    \/ TxADelete
    \/ CachingThread
    \/ TxAWaitDone
    \/ TxASwitchRoots
    \/ TxBSwitchRoots
    \/ TxAUnpin
    \/ Done

Fairness ==
    /\ WF_vars(TxADelete)
    /\ WF_vars(CachingThread)
    /\ WF_vars(TxAWaitDone)
    /\ WF_vars(TxASwitchRoots)
    /\ WF_vars(TxBSwitchRoots)
    /\ WF_vars(TxAUnpin)

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
