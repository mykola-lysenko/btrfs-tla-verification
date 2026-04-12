------------------------- MODULE BtrfsDelayedRefsBuggy2 -------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(*
 * BtrfsDelayedRefsBuggy2.tla — Space Leak Bug
 *
 * This model injects a specific bug: must_insert_reserved is cleared
 * (in a separate step) BEFORE the disk operation runs. A concurrent
 * DROP_DELAYED_REF arriving in this window sees MIR=FALSE and does not
 * trigger the pin_extent path. The result: an extent is allocated
 * (space reserved), then freed before processing, but the space is
 * never returned to the free pool — a space leak.
 *
 * In the correct kernel, must_insert_reserved is read and cleared
 * atomically under head->lock in a single critical section, so no
 * concurrent operation can observe the intermediate state.
 *)

CONSTANTS
    Extents,
    MaxOps

VARIABLES
    disk_extents,
    delayed_refs,
    reserved_bytes,
    pinned_bytes,
    head_processing,
    mir_cleared,       \* BUG: tracks if MIR was cleared early
    space_was_reserved, \* tracks if space was ever reserved for this extent
    ops_count

vars == <<disk_extents, delayed_refs, reserved_bytes, pinned_bytes,
          head_processing, mir_cleared, space_was_reserved, ops_count>>

Init ==
    /\ disk_extents    = [e \in Extents |-> 0]
    /\ delayed_refs    = [e \in Extents |-> <<0, FALSE>>]
    /\ reserved_bytes  = [e \in Extents |-> FALSE]
    /\ pinned_bytes    = [e \in Extents |-> FALSE]
    /\ head_processing = [e \in Extents |-> FALSE]
    /\ mir_cleared        = [e \in Extents |-> FALSE]
    /\ space_was_reserved  = [e \in Extents |-> FALSE]
    /\ ops_count           = 0
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
    /\ ~mir_cleared[e]
    /\ delayed_refs'   = [delayed_refs   EXCEPT ![e] = <<1, TRUE>>]
    /\ reserved_bytes'     = [reserved_bytes     EXCEPT ![e] = TRUE]
    /\ space_was_reserved'  = [space_was_reserved  EXCEPT ![e] = TRUE]
    /\ ops_count'           = ops_count + 1
    /\ UNCHANGED <<disk_extents, pinned_bytes, head_processing, mir_cleared>>

\* BUG: FreeExtent can arrive while MIR has been cleared but disk op not yet run.
\* In this window, the free sees MIR=FALSE and does not set pinned_bytes.
FreeExtent(e) ==
    /\ ops_count < MaxOps
    /\ TotalRefs(e) > 0
    /\ delayed_refs' = [delayed_refs EXCEPT ![e] = <<RefMod(e) - 1, MustInsertReserved(e)>>]
    /\ ops_count'    = ops_count + 1
    /\ UNCHANGED <<disk_extents, reserved_bytes, pinned_bytes, head_processing, mir_cleared, space_was_reserved>>

-----------------------------------------------------------------------------
BeginProcessHead(e) ==
    /\ ~head_processing[e]
    /\ (RefMod(e) /= 0 \/ MustInsertReserved(e))
    /\ head_processing' = [head_processing EXCEPT ![e] = TRUE]
    /\ UNCHANGED <<disk_extents, delayed_refs, reserved_bytes, pinned_bytes, mir_cleared, space_was_reserved, ops_count>>

\* BUG: Clear must_insert_reserved BEFORE running the disk operation
\* This creates a window where a concurrent FreeExtent sees MIR=FALSE
BugClearMIR(e) ==
    /\ head_processing[e]
    /\ MustInsertReserved(e)
    /\ ~mir_cleared[e]
    \* BUG: clear MIR in a separate step before disk op
    /\ delayed_refs' = [delayed_refs EXCEPT ![e] = <<RefMod(e), FALSE>>]
    /\ mir_cleared'  = [mir_cleared  EXCEPT ![e] = TRUE]
    /\ UNCHANGED <<disk_extents, reserved_bytes, pinned_bytes, head_processing, space_was_reserved, ops_count>>

\* Run the delayed ref (disk operation) — but MIR is already FALSE due to BugClearMIR
RunHead(e) ==
    /\ head_processing[e]
    /\ LET rm  == RefMod(e)
           mir == MustInsertReserved(e)  \* BUG: this is now always FALSE
       IN
       /\ disk_extents'  = [disk_extents  EXCEPT ![e] = disk_extents[e] + rm]
       /\ reserved_bytes'= [reserved_bytes EXCEPT ![e] = FALSE]
       /\ pinned_bytes'  = [pinned_bytes   EXCEPT
              \* BUG: mir is FALSE here, so pin_extent never fires
              ![e] = IF rm = 0 /\ mir THEN TRUE ELSE FALSE]
       /\ delayed_refs'  = [delayed_refs   EXCEPT ![e] = <<0, FALSE>>]
       /\ head_processing'  = [head_processing  EXCEPT ![e] = FALSE]
       /\ mir_cleared'   = [mir_cleared    EXCEPT ![e] = FALSE]
    /\ UNCHANGED <<ops_count, space_was_reserved>>

-----------------------------------------------------------------------------

Next ==
    \/ \E e \in Extents: AllocExtent(e)
    \/ \E e \in Extents: FreeExtent(e)
    \/ \E e \in Extents: BeginProcessHead(e)
    \/ \E e \in Extents: BugClearMIR(e)
    \/ \E e \in Extents: RunHead(e)

Fairness ==
    /\ \A e \in Extents: WF_vars(BeginProcessHead(e))
    /\ \A e \in Extents: WF_vars(RunHead(e))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* INVARIANTS

NoNegativeRefs ==
    \A e \in Extents: disk_extents[e] >= 0

\* Space leak detector:
\* If an extent was allocated (reserved_bytes was TRUE) and then freed before
\* processing (ref_mod went to 0), the space MUST be returned to the pool
\* (either pinned_bytes=TRUE or disk_extents > 0).
\* The violation: reserved_bytes=FALSE (cleared), disk_extents=0 (never written),
\* pinned_bytes=FALSE (never pinned) — the space just vanished.
\*
\* We detect this by tracking that if MIR was cleared early AND a free arrived
\* in the window AND the disk op ran with ref_mod=0, then pinned_bytes must be TRUE.
NoSpaceLeak ==
    \A e \in Extents:
        \* After full processing (no pending state)
        (disk_extents[e] = 0 /\ ~reserved_bytes[e] /\ ~head_processing[e] /\
         delayed_refs[e][1] = 0 /\ delayed_refs[e][2] = FALSE /\ ~mir_cleared[e])
        \* If space was ever reserved for this extent, it must be accounted for:
        \* either on disk (ref > 0) or pinned back to free pool
        => (~space_was_reserved[e] \/ disk_extents[e] > 0 \/ pinned_bytes[e])

=============================================================================
