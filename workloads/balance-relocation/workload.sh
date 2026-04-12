#!/usr/bin/env bash
# workloads/balance-relocation/workload.sh
# -----------------------------------------------------------------------
# Stress workload for BtrfsBalanceRelocation.tla (NoLostWrite)
#
# Race window targeted:
#   During balance/relocation, Btrfs moves extents from one block group
#   to another. The race window is between:
#     Relocator: commits the new location (merge_reloc_root)
#     Writer:    writes to the old location (now stale)
#   If a write goes to the old location after relocation commits, the
#   data is lost (the new location has the old data).
#
# What makes this tricky:
#   - The race requires a write to land in the exact block group being
#     relocated, during the relocation window.
#   - We use a targeted approach: run balance on a specific block group
#     while hammering writes to files in that block group.
#   - We use btrfs balance with filters to target specific block groups.
#   - We run balance and writes concurrently from separate processes.
#   - We use O_DIRECT writes to bypass the page cache and go directly
#     to the block layer, maximizing the chance of hitting the window.
#
# Expected trace events:
#   Balance_Start/Done, RelocateBlockGroup_Enter/Done,
#   MergeRelocRoot_Enter/Done, WriteAfterReloc (-> VIOLATION if racing)
#
# Invariant checked: NoLostWrite
#
# Usage:
#   mount -t btrfs /dev/sdb /mnt/btrfs
#   bash workload.sh /mnt/btrfs 180
# -----------------------------------------------------------------------

set -euo pipefail

MOUNT="${1:?Usage: $0 <mount> [duration_secs]}"
DURATION="${2:-180}"
WORKDIR="$MOUNT/balance_stress"
NWRITERS=8

cleanup() {
    echo "[balance] Cleaning up..."
    kill $(jobs -p) 2>/dev/null || true
    wait 2>/dev/null || true
    # Cancel any running balance
    btrfs balance cancel "$MOUNT" 2>/dev/null || true
    rm -rf "$WORKDIR" 2>/dev/null || true
}
trap cleanup EXIT

mkdir -p "$WORKDIR"

# -----------------------------------------------------------------------
# Phase 1: Create files to populate block groups.
# We need at least 2 block groups so balance has something to relocate.
# -----------------------------------------------------------------------
echo "[balance] Phase 1: Populating filesystem..."
for i in $(seq 1 8); do
    dd if=/dev/urandom of="$WORKDIR/data_$i" bs=1M count=128 2>/dev/null
done
sync

# -----------------------------------------------------------------------
# Background writer: continuously writes to files in the data directory.
# Uses O_DIRECT to go directly to the block layer.
# -----------------------------------------------------------------------
writer() {
    local id="$1"
    local file="$WORKDIR/data_$((id % 8 + 1))"
    while true; do
        # Random offset within the file, aligned to 4KB
        local offset=$(( (RANDOM % 32768) * 4096 ))
        dd if=/dev/urandom of="$file" bs=4096 count=1 \
            seek=$(( offset / 4096 )) \
            oflag=direct conv=notrunc 2>/dev/null || true
    done
}

echo "[balance] Phase 2: Starting $NWRITERS concurrent writers..."
for i in $(seq 1 $NWRITERS); do
    writer "$i" &
done

# -----------------------------------------------------------------------
# Main loop: run balance repeatedly while writers are active.
# Each balance run relocates block groups, creating the race window.
# -----------------------------------------------------------------------
echo "[balance] Phase 3: Running balance concurrently with writes for ${DURATION}s."
echo "[balance] Run bpftrace btrfs_balance_relocation.bt in another terminal."

END=$((SECONDS + DURATION))
BALANCES=0
while [ $SECONDS -lt $END ]; do
    # Balance data block groups (most likely to have the race)
    btrfs balance start -dusage=50 "$MOUNT" 2>/dev/null || true
    BALANCES=$((BALANCES + 1))
    echo "[balance] Balance run #$BALANCES complete"
    sleep 2
done

echo "[balance] Done. $BALANCES balance runs. Check bpftrace output."
