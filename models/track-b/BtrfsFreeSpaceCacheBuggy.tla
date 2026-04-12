----------------------- MODULE BtrfsFreeSpaceCacheBuggy -----------------------
EXTENDS Integers, TLC

(*
 * BtrfsFreeSpaceCacheBuggy.tla
 *
 * THE BUG: When a block is freed back to the free space cache, its
 * trim_state is NOT reset to UNTRIMMED. Instead, it keeps its previous
 * TRIMMED state and is NOT added to the discard queue.
 *
 * The bug manifests after the SECOND allocation cycle:
 * Cycle 1: UNTRIMMED -> (discard) -> TRIMMED -> (alloc) -> ALLOCATED
 *          -> (buggy free) -> TRIMMED (not in queue, dirty)
 * Cycle 2: Block is TRIMMED but dirty. Discard worker never picks it up.
 *          NoDiscardLeak violated.
 *
 * We bound alloc_cycles <= MaxCycles to prevent state explosion.
 *)

CONSTANTS MaxCycles

VARIABLES
    block_state,
    discard_queue,
    alloc_thread,
    discard_thread,
    dirty_since_trim,
    alloc_cycles

vars == <<block_state, discard_queue, alloc_thread, discard_thread, dirty_since_trim, alloc_cycles>>

Init ==
    /\ block_state = "UNTRIMMED"
    /\ discard_queue = 1
    /\ alloc_thread = "IDLE"
    /\ discard_thread = "IDLE"
    /\ dirty_since_trim = FALSE
    /\ alloc_cycles = 0

-----------------------------------------------------------------------------

AllocBlock ==
    /\ alloc_thread = "IDLE"
    /\ block_state \in {"UNTRIMMED", "TRIMMED"}
    /\ block_state' = "ALLOCATED"
    /\ discard_queue' = 0
    /\ alloc_thread' = "USING"
    /\ dirty_since_trim' = TRUE
    /\ UNCHANGED <<discard_thread, alloc_cycles>>

\* BUG: does NOT reset trim_state to UNTRIMMED, does NOT add to discard queue
FreeBlockBuggy ==
    /\ alloc_thread = "USING"
    /\ alloc_cycles < MaxCycles
    /\ block_state' = "TRIMMED"  \* BUG: should be "UNTRIMMED"
    /\ discard_queue' = 0        \* BUG: should be 1
    /\ alloc_thread' = "IDLE"
    /\ alloc_cycles' = alloc_cycles + 1
    /\ UNCHANGED <<discard_thread, dirty_since_trim>>

DiscardStart ==
    /\ discard_thread = "IDLE"
    /\ discard_queue = 1
    /\ block_state = "UNTRIMMED"
    /\ block_state' = "TRIMMING"
    /\ discard_queue' = 0
    /\ discard_thread' = "DISCARDING"
    /\ UNCHANGED <<alloc_thread, dirty_since_trim, alloc_cycles>>

DiscardFinish ==
    /\ discard_thread = "DISCARDING"
    /\ block_state = "TRIMMING"
    /\ block_state' = "TRIMMED"
    /\ dirty_since_trim' = FALSE
    /\ discard_thread' = "IDLE"
    /\ UNCHANGED <<discard_queue, alloc_thread, alloc_cycles>>

-----------------------------------------------------------------------------

Next ==
    \/ AllocBlock
    \/ FreeBlockBuggy
    \/ DiscardStart
    \/ DiscardFinish

Fairness ==
    /\ WF_vars(AllocBlock)
    /\ WF_vars(FreeBlockBuggy)
    /\ WF_vars(DiscardStart)
    /\ WF_vars(DiscardFinish)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* PROPERTIES

\* After the buggy free, the block is TRIMMED but dirty_since_trim = TRUE.
\* The discard worker will never pick it up again (not in queue).
\* This liveness property will be violated: the block stays dirty forever.
NoDiscardLeak ==
    (block_state = "TRIMMED" /\ dirty_since_trim = TRUE) ~>
    (block_state = "TRIMMED" /\ dirty_since_trim = FALSE)

SafeTrimming ==
    (block_state = "TRIMMING") => (alloc_thread = "IDLE")

=============================================================================
