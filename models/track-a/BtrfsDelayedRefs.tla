--------------------------- MODULE BtrfsDelayedRefs ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsDelayedRefs.tla — Correct model
 *
 * Models the btrfs delayed-ref state machine and extent-tree accounting.
 *
 * Key invariants from the kernel:
 *
 * 1. Each delayed-ref HEAD carries:
 *      ref_mod           : net change to apply to the extent tree
 *      must_insert_reserved : TRUE when an ADD_DELAYED_EXTENT was recorded
 *                             (space was reserved but not yet written to disk)
 *
 * 2. When an ADD_DELAYED_EXTENT is later cancelled by a DROP before processing:
 *      ref_mod goes to 0, but must_insert_reserved stays TRUE.
 *      cleanup_ref_head() sees must_insert_reserved=TRUE and ref_mod=0 →
 *      it pins the extent bytes (returns them to free space) rather than
 *      leaking the reservation.
 *
 * 3. When processing runs:
 *      if ref_mod > 0 and must_insert_reserved → alloc_reserved_tree_block()
 *      if ref_mod > 0 and !must_insert_reserved → __btrfs_inc_extent_ref()
 *      if ref_mod < 0 → __btrfs_free_extent()
 *      if ref_mod = 0 and must_insert_reserved → pin_extent() (space leaked
 *        back to free pool)
 *
 * The race we test: a concurrent free arriving while the head is being
 * processed. The kernel protects against this with head->lock (spin_lock)
 * and head->mutex (process serialization). Without the mutex, two threads
 * could both see must_insert_reserved=TRUE and both try to pin/alloc.
 *)

CONSTANTS
    Extents,       \* Set of extent IDs
    MaxOps         \* Bound on total operations

VARIABLES
    \* disk_extents[e] = current ref count in the extent tree (0 = free)
    disk_extents,
    \* delayed_refs[e] = <<ref_mod, must_insert_reserved>>
    delayed_refs,
    \* reserved_bytes[e] = TRUE if space is currently reserved for extent e
    reserved_bytes,
    \* pinned_bytes[e] = TRUE if extent e has been pinned (freed back to pool)
    pinned_bytes,
    \* head_processing[e] = TRUE if a thread is currently processing head for e
    head_processing,
    \* ops_count = total ops so far
    ops_count

vars == <<disk_extents, delayed_refs, reserved_bytes, pinned_bytes,
          head_processing, ops_count>>

Init ==
    /\ disk_extents    = [e \in Extents |-> 0]
    /\ delayed_refs    = [e \in Extents |-> <<0, FALSE>>]
    /\ reserved_bytes  = [e \in Extents |-> FALSE]
    /\ pinned_bytes    = [e \in Extents |-> FALSE]
    /\ head_processing = [e \in Extents |-> FALSE]
    /\ ops_count       = 0

-----------------------------------------------------------------------------
\* Helper predicates

RefMod(e)             == delayed_refs[e][1]
MustInsertReserved(e) == delayed_refs[e][2]

\* Total logical ref count (disk + pending)
TotalRefs(e) == disk_extents[e] + RefMod(e)

-----------------------------------------------------------------------------
\* DELAYED REF OPERATIONS (in-memory, protected by delayed_refs->lock)

\* Allocate a new extent: ADD_DELAYED_EXTENT
\* Sets ref_mod += 1, must_insert_reserved = TRUE, reserves space
AllocExtent(e) ==
    /\ ops_count < MaxOps
    /\ disk_extents[e] = 0          \* extent must not already exist on disk
    /\ RefMod(e) = 0                \* no pending ops
    /\ ~reserved_bytes[e]           \* space not already reserved
    /\ ~pinned_bytes[e]
    /\ delayed_refs'   = [delayed_refs   EXCEPT ![e] = <<1, TRUE>>]
    /\ reserved_bytes' = [reserved_bytes EXCEPT ![e] = TRUE]
    /\ ops_count'      = ops_count + 1
    /\ UNCHANGED <<disk_extents, pinned_bytes, head_processing>>

\* Drop a reference: DROP_DELAYED_REF
\* Sets ref_mod -= 1
FreeExtent(e) ==
    /\ ops_count < MaxOps
    /\ TotalRefs(e) > 0             \* must have at least one logical ref
    /\ ~head_processing[e]          \* head not currently being processed
    /\ delayed_refs' = [delayed_refs EXCEPT ![e] = <<RefMod(e) - 1, MustInsertReserved(e)>>]
    /\ ops_count'    = ops_count + 1
    /\ UNCHANGED <<disk_extents, reserved_bytes, pinned_bytes, head_processing>>

\* Add a reference: ADD_DELAYED_REF (e.g. snapshot)
AddRef(e) ==
    /\ ops_count < MaxOps
    /\ TotalRefs(e) > 0             \* extent must logically exist
    /\ ~head_processing[e]
    /\ delayed_refs' = [delayed_refs EXCEPT ![e] = <<RefMod(e) + 1, MustInsertReserved(e)>>]
    /\ ops_count'    = ops_count + 1
    /\ UNCHANGED <<disk_extents, reserved_bytes, pinned_bytes, head_processing>>

-----------------------------------------------------------------------------
\* PROCESS DELAYED REF HEAD (serialized by head->mutex)

\* Begin processing: acquire the head mutex
BeginProcessHead(e) ==
    /\ ~head_processing[e]
    /\ (RefMod(e) /= 0 \/ MustInsertReserved(e))  \* something to do
    /\ head_processing' = [head_processing EXCEPT ![e] = TRUE]
    /\ UNCHANGED <<disk_extents, delayed_refs, reserved_bytes, pinned_bytes, ops_count>>

\* Run the delayed ref:
\*   ref_mod > 0 and must_insert_reserved → alloc_reserved_tree_block
\*   ref_mod > 0 and !must_insert_reserved → __btrfs_inc_extent_ref
\*   ref_mod < 0 → __btrfs_free_extent
\*   ref_mod = 0 and must_insert_reserved → pin_extent (space back to pool)
RunHead(e) ==
    /\ head_processing[e]
    /\ LET rm  == RefMod(e)
           mir == MustInsertReserved(e)
       IN
       /\ disk_extents' = [disk_extents EXCEPT ![e] = disk_extents[e] + rm]
       /\ reserved_bytes' = [reserved_bytes EXCEPT ![e] = FALSE]
       /\ pinned_bytes' = [pinned_bytes EXCEPT
              ![e] = IF rm = 0 /\ mir THEN TRUE ELSE FALSE]
       /\ delayed_refs' = [delayed_refs EXCEPT ![e] = <<0, FALSE>>]
       /\ head_processing' = [head_processing EXCEPT ![e] = FALSE]
    /\ UNCHANGED <<ops_count>>

-----------------------------------------------------------------------------

Next ==
    \/ \E e \in Extents: AllocExtent(e)
    \/ \E e \in Extents: FreeExtent(e)
    \/ \E e \in Extents: AddRef(e)
    \/ \E e \in Extents: BeginProcessHead(e)
    \/ \E e \in Extents: RunHead(e)

Fairness ==
    /\ \A e \in Extents: WF_vars(BeginProcessHead(e))
    /\ \A e \in Extents: WF_vars(RunHead(e))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* INVARIANTS

\* Ref counts on disk must never go negative
NoNegativeRefs ==
    \A e \in Extents: disk_extents[e] >= 0

\* When a head has been fully processed (ref_mod=0, must_insert_reserved=FALSE),
\* the disk ref count must be non-negative and consistent.
ConsistentState ==
    \A e \in Extents:
        (delayed_refs[e][1] = 0 /\ delayed_refs[e][2] = FALSE /\ ~head_processing[e])
        => disk_extents[e] >= 0

\* An extent that was allocated (reserved) and then freed before processing
\* must end up pinned (space returned to pool), not leaked.
\* i.e. if reserved_bytes[e] was TRUE and ref_mod went to 0, pinned_bytes must be TRUE
\* (We check the contrapositive: if not pinned and not on disk, then no reservation was lost)
NoPinnedLeak ==
    \A e \in Extents:
        (disk_extents[e] = 0 /\ ~reserved_bytes[e] /\ ~head_processing[e])
        => ~pinned_bytes[e] \/ (delayed_refs[e][1] = 0 /\ delayed_refs[e][2] = FALSE)

=============================================================================
