---- MODULE BtrfsTransactionRefinement ----
(*
 * Model: Refinement mapping from Concrete to Abstract Transaction Chaining
 *)

EXTENDS BtrfsTransactionConcrete

Abstract == INSTANCE BtrfsTransactionChain WITH
    trans_state      <- trans_state,
    trans_refcount   <- trans_use_count,
    trans_exists     <- trans_allocated,
    writer_state     <- writer_state,
    writer_trans     <- writer_trans,
    committer_state  <- committer_state,
    committer_trans  <- committer_trans,
    ops_count        <- ops_count

Refinement == Abstract!Spec

=============================================================================
