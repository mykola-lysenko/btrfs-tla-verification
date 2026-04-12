---- MODULE BtrfsQgroupRefinement ----
(*
 * Model: Refinement mapping from Concrete to Abstract Qgroup
 *)

EXTENDS BtrfsQgroupConcrete

Abstract == INSTANCE BtrfsQgroup WITH
    extent_size         <- extent_bytes,
    snap_read_size      <- snap_bytes_read,
    qgroup_src          <- src_qgroup_bytes,
    qgroup_snap         <- snap_qgroup_bytes,
    snap_pc             <- snap_state,
    mod_pc              <- mod_state,
    extent_lock         <- IF btrfs_qgroup_lock THEN
                               IF snap_state = "UpdateQgroup" THEN "Snap"
                               ELSE "Mod"
                           ELSE "Free",
    delete_before_read  <- delete_before_read

Refinement == Abstract!FixedSpec

=============================================================================
