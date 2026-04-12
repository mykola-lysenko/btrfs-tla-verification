---- MODULE BtrfsRAID56Concrete ----
(*
 * Model: Concrete Btrfs RAID56 Write Intent
 *
 * This model is a detailed representation of fs/btrfs/raid56.c
 * write_stripe and raid56_parity_recover.
 *)

EXTENDS Integers, TLC

VARIABLES
    \* Concrete variables
    bio_data_sector,      \* "Old" or "New"
    bio_parity_sector,    \* "Old" or "New"
    btrfs_journal_state,  \* 0 = Empty, 1 = Intent, 2 = Done
    
    \* System state
    system_power_failed,  \* BOOLEAN
    raid_thread_state

vars == <<bio_data_sector, bio_parity_sector, btrfs_journal_state,
          system_power_failed, raid_thread_state>>

Init ==
    /\ bio_data_sector = "Old"
    /\ bio_parity_sector = "Old"
    /\ btrfs_journal_state = 0
    /\ system_power_failed = FALSE
    /\ raid_thread_state = "Init"

WriteIntent ==
    /\ raid_thread_state = "Init"
    /\ system_power_failed = FALSE
    /\ btrfs_journal_state' = 1
    /\ raid_thread_state' = "WriteData"
    /\ UNCHANGED <<bio_data_sector, bio_parity_sector, system_power_failed>>

WriteData ==
    /\ raid_thread_state = "WriteData"
    /\ system_power_failed = FALSE
    /\ bio_data_sector' = "New"
    /\ raid_thread_state' = "WriteParity"
    /\ UNCHANGED <<bio_parity_sector, system_power_failed, btrfs_journal_state>>

WriteParity ==
    /\ raid_thread_state = "WriteParity"
    /\ system_power_failed = FALSE
    /\ bio_parity_sector' = "New"
    /\ raid_thread_state' = "ClearIntent"
    /\ UNCHANGED <<bio_data_sector, system_power_failed, btrfs_journal_state>>

ClearIntent ==
    /\ raid_thread_state = "ClearIntent"
    /\ system_power_failed = FALSE
    /\ btrfs_journal_state' = 2
    /\ raid_thread_state' = "Done"
    /\ UNCHANGED <<bio_data_sector, bio_parity_sector, system_power_failed>>

PowerLoss ==
    /\ system_power_failed = FALSE
    /\ raid_thread_state \in {"WriteData", "WriteParity", "ClearIntent"}
    /\ system_power_failed' = TRUE
    /\ raid_thread_state' = "Recover"
    /\ UNCHANGED <<bio_data_sector, bio_parity_sector, btrfs_journal_state>>

Recover ==
    /\ raid_thread_state = "Recover"
    /\ system_power_failed = TRUE
    /\ IF btrfs_journal_state = 1 THEN
           /\ bio_parity_sector' = bio_data_sector
           /\ btrfs_journal_state' = 2
       ELSE
           /\ UNCHANGED <<bio_parity_sector, btrfs_journal_state>>
    /\ raid_thread_state' = "Done"
    /\ UNCHANGED <<bio_data_sector, system_power_failed>>

Done ==
    /\ raid_thread_state = "Done"
    /\ UNCHANGED vars

Next ==
    \/ WriteIntent
    \/ WriteData
    \/ WriteParity
    \/ ClearIntent
    \/ PowerLoss
    \/ Recover
    \/ Done

Fairness ==
    /\ WF_vars(WriteIntent)
    /\ WF_vars(WriteData)
    /\ WF_vars(WriteParity)
    /\ WF_vars(ClearIntent)
    /\ WF_vars(Recover)

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================
