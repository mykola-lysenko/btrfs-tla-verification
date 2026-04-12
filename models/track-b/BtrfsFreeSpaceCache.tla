---------------------------- MODULE BtrfsFreeSpaceCache ----------------------------
(*
 * Model: Btrfs Free Space Cache v2 double-add race (commit ced8ecf026fd)
 *
 * Bug: Asynchronous block group caching races with unpin_extent_range().
 *
 * Key insight from the commit:
 *   - The caching thread reads from the COMMIT ROOT (switched by switch_commit_roots).
 *   - unpin_extent_range() adds extents to the cache if offset < last_byte_to_unpin.
 *   - last_byte_to_unpin is set to bg->progress at switch_commit_roots time.
 *   - bg->progress starts at bg->start (0) and becomes U64_MAX (1) when caching finishes.
 *
 * Buggy sequence:
 *  1. Tx A deletes extent, queues async caching (bg->progress = 0).
 *  2. Tx A switch_commit_roots: last_byte_to_unpin = 0 (caching not done yet).
 *  3. Caching thread runs: reads NEW commit root, sees extent as free, adds to cache.
 *     bg->progress = 1.
 *  4. Tx A reaches SUPER_COMMITTED.
 *  5. Tx B switch_commit_roots: last_byte_to_unpin = 1 (caching done).
 *  6. Tx A unpin: sees last_byte_to_unpin = 1 (set by Tx B!), adds extent again -> BUG.
 *
 * Fixed sequence:
 *  1. Tx A deletes extent, caching runs SYNCHRONOUSLY (bg->progress = 1).
 *  2. But caching reads OLD commit root (before switch), so extent NOT yet free -> does NOT add.
 *  3. Tx A switch_commit_roots: last_byte_to_unpin = 1 (caching already done).
 *  4. Tx A reaches SUPER_COMMITTED.
 *  5. Tx B switch_commit_roots: last_byte_to_unpin = 1 (same, no change).
 *  6. Tx A unpin: sees last_byte_to_unpin = 1, adds extent ONCE -> correct.
 *
 * Variables:
 *   bg_progress: 0 = start, 1 = U64_MAX (caching done)
 *   bg_last_byte_to_unpin: 0 or 1 (set by switch_commit_roots)
 *   space_cache_count: how many times the extent was added to space cache
 *   caching_reads_new_root: TRUE if caching thread reads the new commit root (buggy)
 *)

EXTENDS Integers, TLC

VARIABLES
    bg_progress,
    bg_last_byte_to_unpin,
    space_cache_count,
    commit_root_switched,
    tx_a_pc,
    tx_b_pc,
    caching_thread_pc

vars == <<bg_progress, bg_last_byte_to_unpin, space_cache_count,
          commit_root_switched, tx_a_pc, tx_b_pc, caching_thread_pc>>

Init ==
    /\ bg_progress = 0
    /\ bg_last_byte_to_unpin = 0
    /\ space_cache_count = 0
    /\ commit_root_switched = FALSE
    /\ tx_a_pc = "Init"
    /\ tx_b_pc = "Init"
    /\ caching_thread_pc = "Init"

(* ===========================================================================
 * BUGGY VARIANT: Asynchronous caching
 * =========================================================================== *)

\* Tx A: delete extent, queue async caching
BuggyTxADelete ==
    /\ tx_a_pc = "Init"
    /\ caching_thread_pc' = "Cache"
    /\ tx_a_pc' = "SwitchRoots"
    /\ UNCHANGED <<bg_progress, bg_last_byte_to_unpin, space_cache_count, commit_root_switched, tx_b_pc>>

\* Tx A: switch commit roots (caching may or may not be done)
BuggyTxASwitchRoots ==
    /\ tx_a_pc = "SwitchRoots"
    /\ bg_last_byte_to_unpin' = bg_progress
    /\ commit_root_switched' = TRUE
    /\ tx_a_pc' = "SuperCommitted"
    /\ UNCHANGED <<bg_progress, space_cache_count, tx_b_pc, caching_thread_pc>>

\* Caching thread: reads NEW commit root (after switch), sees deleted extent as free
BuggyCachingThreadCache ==
    /\ caching_thread_pc = "Cache"
    /\ commit_root_switched = TRUE   \* BUG: caching runs after switch_commit_roots
    /\ space_cache_count' = space_cache_count + 1
    /\ bg_progress' = 1
    /\ caching_thread_pc' = "Done"
    /\ UNCHANGED <<bg_last_byte_to_unpin, commit_root_switched, tx_a_pc, tx_b_pc>>

\* Tx B: switch commit roots (sees bg->progress = 1 since caching is done)
BuggyTxBSwitchRoots ==
    /\ tx_b_pc = "Init"
    /\ tx_a_pc \in {"SuperCommitted", "Done"}
    /\ bg_last_byte_to_unpin' = bg_progress
    /\ tx_b_pc' = "Done"
    /\ UNCHANGED <<bg_progress, space_cache_count, commit_root_switched, tx_a_pc, caching_thread_pc>>

\* Tx A: unpin extent (adds to cache if last_byte_to_unpin = 1)
BuggyTxAUnpin ==
    /\ tx_a_pc = "SuperCommitted"
    /\ space_cache_count' = IF bg_last_byte_to_unpin = 1
                             THEN space_cache_count + 1
                             ELSE space_cache_count
    /\ tx_a_pc' = "Done"
    /\ UNCHANGED <<bg_progress, bg_last_byte_to_unpin, commit_root_switched, tx_b_pc, caching_thread_pc>>

BuggyDone ==
    /\ tx_a_pc = "Done"
    /\ tx_b_pc = "Done"
    /\ caching_thread_pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyTxADelete
    \/ BuggyTxASwitchRoots
    \/ BuggyCachingThreadCache
    \/ BuggyTxBSwitchRoots
    \/ BuggyTxAUnpin
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyTxADelete)
    /\ WF_vars(BuggyTxASwitchRoots)
    /\ WF_vars(BuggyCachingThreadCache)
    /\ WF_vars(BuggyTxBSwitchRoots)
    /\ WF_vars(BuggyTxAUnpin)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Synchronous caching (runs BEFORE switch_commit_roots)
 * =========================================================================== *)

\* Tx A: delete extent, wait for caching synchronously
FixedTxADelete ==
    /\ tx_a_pc = "Init"
    /\ caching_thread_pc' = "Cache"
    /\ tx_a_pc' = "WaitCache"
    /\ UNCHANGED <<bg_progress, bg_last_byte_to_unpin, space_cache_count, commit_root_switched, tx_b_pc>>

\* Caching thread: reads OLD commit root (before switch), does NOT see deleted extent
FixedCachingThreadCache ==
    /\ caching_thread_pc = "Cache"
    /\ commit_root_switched = FALSE  \* FIX: caching runs before switch_commit_roots
    \* Does NOT add to space_cache_count because commit root not yet switched
    /\ bg_progress' = 1
    /\ caching_thread_pc' = "Done"
    /\ UNCHANGED <<bg_last_byte_to_unpin, space_cache_count, commit_root_switched, tx_a_pc, tx_b_pc>>

\* Tx A: wait for caching to complete, then proceed
FixedTxAWaitDone ==
    /\ tx_a_pc = "WaitCache"
    /\ caching_thread_pc = "Done"
    /\ tx_a_pc' = "SwitchRoots"
    /\ UNCHANGED <<bg_progress, bg_last_byte_to_unpin, space_cache_count, commit_root_switched, tx_b_pc, caching_thread_pc>>

\* Tx A: switch commit roots (bg->progress = 1 since caching is done)
FixedTxASwitchRoots ==
    /\ tx_a_pc = "SwitchRoots"
    /\ bg_last_byte_to_unpin' = bg_progress
    /\ commit_root_switched' = TRUE
    /\ tx_a_pc' = "SuperCommitted"
    /\ UNCHANGED <<bg_progress, space_cache_count, tx_b_pc, caching_thread_pc>>

\* Tx B: switch commit roots
FixedTxBSwitchRoots ==
    /\ tx_b_pc = "Init"
    /\ tx_a_pc \in {"SuperCommitted", "Done"}
    /\ bg_last_byte_to_unpin' = bg_progress
    /\ tx_b_pc' = "Done"
    /\ UNCHANGED <<bg_progress, space_cache_count, commit_root_switched, tx_a_pc, caching_thread_pc>>

\* Tx A: unpin extent
FixedTxAUnpin ==
    /\ tx_a_pc = "SuperCommitted"
    /\ space_cache_count' = IF bg_last_byte_to_unpin = 1
                             THEN space_cache_count + 1
                             ELSE space_cache_count
    /\ tx_a_pc' = "Done"
    /\ UNCHANGED <<bg_progress, bg_last_byte_to_unpin, commit_root_switched, tx_b_pc, caching_thread_pc>>

FixedDone ==
    /\ tx_a_pc = "Done"
    /\ tx_b_pc = "Done"
    /\ caching_thread_pc = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedTxADelete
    \/ FixedCachingThreadCache
    \/ FixedTxAWaitDone
    \/ FixedTxASwitchRoots
    \/ FixedTxBSwitchRoots
    \/ FixedTxAUnpin
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedTxADelete)
    /\ WF_vars(FixedCachingThreadCache)
    /\ WF_vars(FixedTxAWaitDone)
    /\ WF_vars(FixedTxASwitchRoots)
    /\ WF_vars(FixedTxBSwitchRoots)
    /\ WF_vars(FixedTxAUnpin)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Invariants
 * =========================================================================== *)

NoDoubleAdd ==
    space_cache_count <= 1

==============================================================================
