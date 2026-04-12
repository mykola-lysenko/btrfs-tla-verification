---- MODULE BtrfsRAID56Refinement ----
(*
 * Model: Refinement mapping from Concrete to Abstract RAID56
 *)

EXTENDS BtrfsRAID56Concrete

Abstract == INSTANCE BtrfsRAID56 WITH
    disk_data   <- bio_data_sector,
    disk_parity <- bio_parity_sector,
    pc          <- raid_thread_state,
    power_loss  <- system_power_failed,
    journal     <- IF btrfs_journal_state = 0 THEN "Empty"
                   ELSE IF btrfs_journal_state = 1 THEN "Intent"
                   ELSE "Done"

Refinement == Abstract!FixedSpec

=============================================================================
