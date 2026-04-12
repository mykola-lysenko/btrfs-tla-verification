-------------------------- MODULE BtrfsDelayedRefsBuggy --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsDelayedRefsBuggy.tla — Buggy model
 *
 * This model injects two bugs into the delayed-ref processing:
 *
 * BUG 1: Missing head->mutex serialization.
 *   Two concurrent threads can both enter RunHead() for the same extent.
 *   In the correct kernel, head->mutex prevents this. Without it, both
 *   threads see must_insert_reserved=TRUE and both try to call
 *   alloc_reserved_tree_block(), causing a double-allocation on disk.
 *
 * BUG 2: must_insert_reserved cleared before ref_mod is processed.
 *   In the correct kernel, must_insert_reserved is read and then cleared
 *   atomically under head->lock before the actual disk operation.
 *   In the buggy model, must_insert_reserved is cleared first (in a
 *   separate step), then the disk operation runs. A concurrent DROP
 *   arriving between these two steps sees must_insert_reserved=FALSE
 *   and does NOT trigger the pin_extent path, causing a space leak.
 *)

CONSTANTS
    Extents,       \* Set of extent IDs
    MaxOps         \* Bound on total operations

VARIABLES
    disk_extents,
    delayed_refs,
    reserved_bytes,
    pinned_bytes,
    head_processing,
    \* BUG 1: track how many threads are "processing" the same head
    processing_count,
    ops_count

vars == <<disk_extents, delayed_refs, reserved_bytes, pinned_bytes,
          head_processing, processing_count, ops_count>>

Init ==
    /\ disk_extents    = [e \in Extents |-> 0]
    /\ delayed_refs    = [e \in Extents |-> <<0, FALSE>>]
    /\ reserved_bytes  = [e \in Extents |-> FALSE]
    /\ pinned_bytes    = [e \in Extents |-> FALSE]
    /\ head_processing = [e \in Extents |-> FALSE]
    /\ processing_count = [e \in Extents |-> 0]
    /\ ops_count       = 0

-----------------------------------------------------------------------------
RefMod(e)             == delayed_refs[e][1]
MustInsertReserved(e) == delayed_refs[e][2]
TotalRefs(e)          == disk_extents[e] + RefMod(e)

-----------------------------------------------------------------------------
AllocExtent(e) ==
    /\ ops_count < MaxOps
    /\ disk_extents[e] = 0
    /\ RefMod(e) = 0
    /\ ~reserved_bytes[e]
    /\ ~pinned_bytes[e]
    /\ delayed_refs'   = [delayed_refs   EXCEPT ![e] = <<1, TRUE>>]
    /\ reserved_bytes' = [reserved_bytes EXCEPT ![e] = TRUE]
    /\ ops_count'      = ops_count + 1
    /\ UNCHANGED <<disk_extents, pinned_bytes, head_processing, processing_count>>

FreeExtent(e) ==
    /\ ops_count < MaxOps
    /\ TotalRefs(e) > 0
    \* BUG: no check for head_processing — free can arrive while head is being processed
    /\ delayed_refs' = [delayed_refs EXCEPT ![e] = <<RefMod(e) - 1, MustInsertReserved(e)>>]
    /\ ops_count'    = ops_count + 1
    /\ UNCHANGED <<disk_extents, reserved_bytes, pinned_bytes, head_processing, processing_count>>

AddRef(e) ==
    /\ ops_count < MaxOps
    /\ TotalRefs(e) > 0
    /\ delayed_refs' = [delayed_refs EXCEPT ![e] = <<RefMod(e) + 1, MustInsertReserved(e)>>]
    /\ ops_count'    = ops_count + 1
    /\ UNCHANGED <<disk_extents, reserved_bytes, pinned_bytes, head_processing, processing_count>>

-----------------------------------------------------------------------------
\* BUG 1: No mutex — multiple threads can begin processing the same head
BeginProcessHead(e) ==
    \* BUG: no check for head_processing[e] — multiple threads can enter
    /\ (RefMod(e) /= 0 \/ MustInsertReserved(e))
    /\ head_processing'  = [head_processing  EXCEPT ![e] = TRUE]
    /\ processing_count' = [processing_count EXCEPT ![e] = processing_count[e] + 1]
    /\ UNCHANGED <<disk_extents, delayed_refs, reserved_bytes, pinned_bytes, ops_count>>

\* BUG 2: must_insert_reserved is cleared in a separate step before disk op
\* This creates a window where a concurrent FreeExtent sees MIR=FALSE
ClearMustInsertReserved(e) ==
    /\ head_processing[e]
    /\ MustInsertReserved(e)
    \* BUG: clear MIR before running the disk operation
    /\ delayed_refs' = [delayed_refs EXCEPT ![e] = <<RefMod(e), FALSE>>]
    /\ UNCHANGED <<disk_extents, reserved_bytes, pinned_bytes, head_processing, processing_count, ops_count>>

\* Run the delayed ref (disk operation)
RunHead(e) ==
    /\ head_processing[e]
    /\ LET rm  == RefMod(e)
           mir == MustInsertReserved(e)
       IN
       /\ disk_extents'  = [disk_extents  EXCEPT ![e] = disk_extents[e] + rm]
       /\ reserved_bytes'= [reserved_bytes EXCEPT ![e] = FALSE]
       /\ pinned_bytes'  = [pinned_bytes   EXCEPT
              ![e] = IF rm = 0 /\ mir THEN TRUE ELSE FALSE]
       /\ delayed_refs'  = [delayed_refs   EXCEPT ![e] = <<0, FALSE>>]
       /\ head_processing'  = [head_processing  EXCEPT ![e] = FALSE]
       /\ processing_count' = [processing_count EXCEPT ![e] = 0]
    /\ UNCHANGED <<ops_count>>

-----------------------------------------------------------------------------

Next ==
    \/ \E e \in Extents: AllocExtent(e)
    \/ \E e \in Extents: FreeExtent(e)
    \/ \E e \in Extents: AddRef(e)
    \/ \E e \in Extents: BeginProcessHead(e)
    \/ \E e \in Extents: ClearMustInsertReserved(e)
    \/ \E e \in Extents: RunHead(e)

Fairness ==
    /\ \A e \in Extents: WF_vars(BeginProcessHead(e))
    /\ \A e \in Extents: WF_vars(RunHead(e))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* INVARIANTS

NoNegativeRefs ==
    \A e \in Extents: disk_extents[e] >= 0

ConsistentState ==
    \A e \in Extents:
        (delayed_refs[e][1] = 0 /\ delayed_refs[e][2] = FALSE /\ ~head_processing[e])
        => disk_extents[e] >= 0

\* BUG 1 detector: no two threads should process the same head simultaneously
NoDoubleProcessing ==
    \A e \in Extents: processing_count[e] <= 1

=============================================================================
