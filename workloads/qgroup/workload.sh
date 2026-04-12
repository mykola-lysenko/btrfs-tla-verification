#!/usr/bin/env bash
# workloads/qgroup/workload.sh
# -----------------------------------------------------------------------
# Stress workload for BtrfsQgroup.tla (CVE-2025-39759)
#
# Race window targeted:
#   btrfs_free_qgroup_config() frees qgroup records from qgroup_tree
#   WITHOUT holding qgroup_lock, while qgroup_rescan_zero_tracking()
#   iterates the same tree WITH the lock held.
#
#   The race requires:
#     Thread A: btrfs_quota_enable  -> btrfs_qgroup_rescan (worker starts)
#     Thread B: btrfs_quota_disable -> btrfs_free_qgroup_config
#   where Thread B's free races with Thread A's rescan iteration.
#
# What makes this tricky:
#   - The rescan worker is asynchronous: it starts on a workqueue, so
#     the window between quota_enable and the worker actually running
#     is small and timing-dependent.
#   - We hammer enable/disable in a tight loop from two processes to
#     maximize the chance of hitting the window.
#   - We also run a continuous file creation workload to keep the
#     qgroup accounting active, which makes the rescan take longer
#     and widens the race window.
#   - The subvolume creation forces qgroup inheritance, which adds
#     more qgroup_tree operations during the race window.
#
# Expected trace events:
#   QuotaEnable_Done, QgroupRescan_Enter, RescanZeroTracking_Enter,
#   QuotaDisable_Enter, FreeQgroupConfig_Enter (-> VIOLATION if racing)
#
# Invariant checked: NoUAF
#
# Usage:
#   mount -t btrfs /dev/sdb /mnt/btrfs
#   bash workload.sh /mnt/btrfs 60
# -----------------------------------------------------------------------

set -euo pipefail

MOUNT="${1:?Usage: $0 <mount> [duration_secs]}"
DURATION="${2:-60}"
WORKDIR="$MOUNT/qgroup_stress"

cleanup() {
    echo "[qgroup] Cleaning up..."
    kill $(jobs -p) 2>/dev/null || true
    wait 2>/dev/null || true
    # Disable quotas before unmount
    btrfs quota disable "$MOUNT" 2>/dev/null || true
    rm -rf "$WORKDIR" 2>/dev/null || true
}
trap cleanup EXIT

mkdir -p "$WORKDIR"

echo "[qgroup] Phase 1: Create subvolumes to populate qgroup tree"
for i in $(seq 1 8); do
    btrfs subvolume create "$WORKDIR/subvol_$i" 2>/dev/null || true
done

# -----------------------------------------------------------------------
# Background job 1: File creation workload
# Keeps the qgroup accounting busy so rescan takes longer (wider window).
# -----------------------------------------------------------------------
file_creator() {
    local dir="$1"
    while true; do
        dd if=/dev/urandom of="$dir/f_$$_$RANDOM" bs=4096 count=$((RANDOM % 32 + 1)) \
            2>/dev/null
        sync
        sleep 0.05
    done
}

for i in $(seq 1 4); do
    file_creator "$WORKDIR/subvol_$((i % 8 + 1))" &
done

# -----------------------------------------------------------------------
# Background job 2: Subvolume snapshot creation
# Forces qgroup inheritance operations during the race window.
# -----------------------------------------------------------------------
snapshot_creator() {
    local n=0
    while true; do
        btrfs subvolume snapshot "$WORKDIR/subvol_1" \
            "$WORKDIR/snap_$n" 2>/dev/null || true
        sleep 0.1
        btrfs subvolume delete "$WORKDIR/snap_$n" 2>/dev/null || true
        n=$((n + 1))
    done
}
snapshot_creator &

# -----------------------------------------------------------------------
# Main race loop: enable quotas, trigger rescan, immediately disable
# The goal is to have the rescan worker running when disable fires.
# -----------------------------------------------------------------------
echo "[qgroup] Phase 2: Racing quota enable/disable for ${DURATION}s"
echo "[qgroup] Run bpftrace btrfs_qgroup.bt in another terminal to capture trace."

END=$((SECONDS + DURATION))
RACES=0
while [ $SECONDS -lt $END ]; do
    # Enable quotas — this starts the qgroup tree
    btrfs quota enable "$MOUNT" 2>/dev/null || true

    # Trigger a rescan — this starts the async worker
    btrfs quota rescan "$MOUNT" 2>/dev/null || true

    # Immediately disable — races with the rescan worker
    # The shorter the sleep, the tighter the race window
    sleep 0.02
    btrfs quota disable "$MOUNT" 2>/dev/null || true

    RACES=$((RACES + 1))
    if [ $((RACES % 10)) -eq 0 ]; then
        echo "[qgroup] $RACES enable/disable cycles completed"
    fi
done

echo "[qgroup] Done. $RACES enable/disable cycles. Check bpftrace output."
