---------------------------- MODULE BtrfsDelayedInode ----------------------------
(*
 * Model: Btrfs delayed inode eviction vs delayed ref processing ABBA deadlock
 *
 * Bug description:
 * When an inode is evicted, `btrfs_evict_inode` needs to delete the inode item
 * from the B-tree. It first locks the delayed node mutex, then attempts to lock
 * a B-tree node. Concurrently, a transaction commit thread holds a B-tree node
 * lock and needs to update the delayed inode, requiring the delayed node mutex.
 * This causes an ABBA deadlock.
 *
 * Sequence (buggy):
 * 1. Evict thread locks delayed_node_mutex.
 * 2. Commit thread locks btree_node_lock.
 * 3. Evict thread tries to lock btree_node_lock -> blocks.
 * 4. Commit thread tries to lock delayed_node_mutex -> blocks (Deadlock).
 *
 * Fix: Enforce strict lock ordering: always acquire btree_node_lock before
 * delayed_node_mutex. This prevents the ABBA cycle.
 *
 * Variables:
 *   delayed_node_mutex: "Free" | "Evict" | "Commit"
 *   btree_node_lock: "Free" | "Evict" | "Commit"
 *   evict_pc: "Init" | "HoldDelayed" | "HoldBoth" | "Release" | "Done"
 *   commit_pc: "Init" | "HoldBtree" | "HoldBoth" | "Release" | "Done"
 *
 * Invariant: NoDeadlock (TLC deadlock detection)
 *)

EXTENDS Integers, TLC

VARIABLES
    delayed_node_mutex,
    btree_node_lock,
    evict_pc,
    commit_pc

vars == <<delayed_node_mutex, btree_node_lock, evict_pc, commit_pc>>

Init ==
    /\ delayed_node_mutex = "Free"
    /\ btree_node_lock = "Free"
    /\ evict_pc = "Init"
    /\ commit_pc = "Init"

(* ===========================================================================
 * BUGGY VARIANT: Evict locks Delayed first, then Btree (ABBA with Commit)
 *                Commit locks Btree first, then Delayed
 * =========================================================================== *)

BuggyEvictLockDelayed ==
    /\ evict_pc = "Init"
    /\ delayed_node_mutex = "Free"
    /\ delayed_node_mutex' = "Evict"
    /\ evict_pc' = "HoldDelayed"
    /\ UNCHANGED <<btree_node_lock, commit_pc>>

BuggyEvictLockBtree ==
    /\ evict_pc = "HoldDelayed"
    /\ btree_node_lock = "Free"
    /\ btree_node_lock' = "Evict"
    /\ evict_pc' = "HoldBoth"
    /\ UNCHANGED <<delayed_node_mutex, commit_pc>>

BuggyEvictRelease ==
    /\ evict_pc = "HoldBoth"
    /\ delayed_node_mutex' = "Free"
    /\ btree_node_lock' = "Free"
    /\ evict_pc' = "Done"
    /\ UNCHANGED <<commit_pc>>

BuggyCommitLockBtree ==
    /\ commit_pc = "Init"
    /\ btree_node_lock = "Free"
    /\ btree_node_lock' = "Commit"
    /\ commit_pc' = "HoldBtree"
    /\ UNCHANGED <<delayed_node_mutex, evict_pc>>

BuggyCommitLockDelayed ==
    /\ commit_pc = "HoldBtree"
    /\ delayed_node_mutex = "Free"
    /\ delayed_node_mutex' = "Commit"
    /\ commit_pc' = "HoldBoth"
    /\ UNCHANGED <<btree_node_lock, evict_pc>>

BuggyCommitRelease ==
    /\ commit_pc = "HoldBoth"
    /\ delayed_node_mutex' = "Free"
    /\ btree_node_lock' = "Free"
    /\ commit_pc' = "Done"
    /\ UNCHANGED <<evict_pc>>

BuggyDone ==
    /\ evict_pc = "Done"
    /\ commit_pc = "Done"
    /\ UNCHANGED vars

BuggyNext ==
    \/ BuggyEvictLockDelayed
    \/ BuggyEvictLockBtree
    \/ BuggyEvictRelease
    \/ BuggyCommitLockBtree
    \/ BuggyCommitLockDelayed
    \/ BuggyCommitRelease
    \/ BuggyDone

BuggyFairness ==
    /\ WF_vars(BuggyEvictLockDelayed)
    /\ WF_vars(BuggyEvictLockBtree)
    /\ WF_vars(BuggyEvictRelease)
    /\ WF_vars(BuggyCommitLockBtree)
    /\ WF_vars(BuggyCommitLockDelayed)
    /\ WF_vars(BuggyCommitRelease)

BuggySpec == Init /\ [][BuggyNext]_vars /\ BuggyFairness

(* ===========================================================================
 * FIXED VARIANT: Both threads lock in same order: Btree first, then Delayed
 * =========================================================================== *)

FixedEvictLockBtree ==
    /\ evict_pc = "Init"
    /\ btree_node_lock = "Free"
    /\ btree_node_lock' = "Evict"
    /\ evict_pc' = "HoldBtree"
    /\ UNCHANGED <<delayed_node_mutex, commit_pc>>

FixedEvictLockDelayed ==
    /\ evict_pc = "HoldBtree"
    /\ delayed_node_mutex = "Free"
    /\ delayed_node_mutex' = "Evict"
    /\ evict_pc' = "HoldBoth"
    /\ UNCHANGED <<btree_node_lock, commit_pc>>

FixedEvictRelease ==
    /\ evict_pc = "HoldBoth"
    /\ delayed_node_mutex' = "Free"
    /\ btree_node_lock' = "Free"
    /\ evict_pc' = "Done"
    /\ UNCHANGED <<commit_pc>>

FixedCommitLockBtree ==
    /\ commit_pc = "Init"
    /\ btree_node_lock = "Free"
    /\ btree_node_lock' = "Commit"
    /\ commit_pc' = "HoldBtree"
    /\ UNCHANGED <<delayed_node_mutex, evict_pc>>

FixedCommitLockDelayed ==
    /\ commit_pc = "HoldBtree"
    /\ delayed_node_mutex = "Free"
    /\ delayed_node_mutex' = "Commit"
    /\ commit_pc' = "HoldBoth"
    /\ UNCHANGED <<btree_node_lock, evict_pc>>

FixedCommitRelease ==
    /\ commit_pc = "HoldBoth"
    /\ delayed_node_mutex' = "Free"
    /\ btree_node_lock' = "Free"
    /\ commit_pc' = "Done"
    /\ UNCHANGED <<evict_pc>>

FixedDone ==
    /\ evict_pc = "Done"
    /\ commit_pc = "Done"
    /\ UNCHANGED vars

FixedNext ==
    \/ FixedEvictLockBtree
    \/ FixedEvictLockDelayed
    \/ FixedEvictRelease
    \/ FixedCommitLockBtree
    \/ FixedCommitLockDelayed
    \/ FixedCommitRelease
    \/ FixedDone

FixedFairness ==
    /\ WF_vars(FixedEvictLockBtree)
    /\ WF_vars(FixedEvictLockDelayed)
    /\ WF_vars(FixedEvictRelease)
    /\ WF_vars(FixedCommitLockBtree)
    /\ WF_vars(FixedCommitLockDelayed)
    /\ WF_vars(FixedCommitRelease)

FixedSpec == Init /\ [][FixedNext]_vars /\ FixedFairness

(* ===========================================================================
 * Liveness Properties (Track E)
 * =========================================================================== *)

\* Both threads eventually complete.
\* This proves that the strict lock ordering doesn't just prevent deadlocks,
\* but actually allows both threads to make progress and finish.
EventualCompletion ==
    <>(evict_pc = "Done" /\ commit_pc = "Done")

==============================================================================
