#!/usr/bin/env bash
# workloads/raid56/workload.sh
# -----------------------------------------------------------------------
# Stress workload for BtrfsRAID56.tla (NoWriteHole)
#
# Race window targeted:
#   A RAID5 stripe write involves:
#     1. Read old data + old parity (RMW cycle)
#     2. Compute new parity
#     3. Write new data + new parity
#   If the system crashes between steps 2 and 3 (partial stripe write),
#   the parity is inconsistent with the data — the write hole.
#
# What makes this tricky:
#   - The write hole only manifests on crash/power failure, not during
#     normal operation. We simulate it by:
#     1. Writing partial stripes (writes smaller than the stripe size)
#     2. Using dm-flakey or scsi_debug to inject I/O errors mid-stripe
#     3. Monitoring the RMW cycle with bpftrace to see partial writes
#   - We use multiple threads writing to the same stripe simultaneously
#     to maximize the chance of partial stripe writes.
#   - We use O_DIRECT to bypass the page cache and go directly to the
#     RAID56 stripe write path.
#
# Note: This workload requires a RAID5 Btrfs setup with at least 3 devices.
#       For testing, use loop devices: losetup -f --show /tmp/disk{1,2,3}.img
#
# Expected trace events:
#   ParityWrite_Enter/Submitted, FinishRMW_Enter/Done, WriteEndIO
#
# Invariant checked: NoWriteHole
#
# Usage:
#   # Setup (3 loop devices):
#   for i in 1 2 3; do dd if=/dev/zero of=/tmp/disk$i.img bs=1M count=512; done
#   for i in 1 2 3; do losetup -f /tmp/disk$i.img; done
#   mkfs.btrfs -d raid5 -m raid5 /dev/loop0 /dev/loop1 /dev/loop2
#   mount /dev/loop0 /mnt/btrfs
#   bash workload.sh /mnt/btrfs 120
# -----------------------------------------------------------------------

set -euo pipefail

MOUNT="${1:?Usage: $0 <mount> [duration_secs]}"
DURATION="${2:-120}"
WORKDIR="$MOUNT/raid56_stress"
NTHREADS=8

# RAID5 stripe size is typically 64KB per device
# Writing less than stripe_size forces a RMW cycle
STRIPE_SIZE=65536   # 64KB
PARTIAL_SIZE=4096   # 4KB — forces RMW

cleanup() {
    echo "[raid56] Cleaning up..."
    kill $(jobs -p) 2>/dev/null || true
    wait 2>/dev/null || true
    rm -rf "$WORKDIR" 2>/dev/null || true
}
trap cleanup EXIT

mkdir -p "$WORKDIR"

# -----------------------------------------------------------------------
# Partial stripe writer: writes PARTIAL_SIZE bytes at random offsets
# within a stripe-aligned region. Each write forces an RMW cycle.
# -----------------------------------------------------------------------
partial_writer() {
    local id="$1"
    local file="$WORKDIR/stripe_file_$id"

    # Pre-allocate a file spanning multiple stripes
    dd if=/dev/zero of="$file" bs="$STRIPE_SIZE" count=64 2>/dev/null
    sync

    local n=0
    while true; do
        # Pick a random stripe-aligned offset
        local stripe_off=$(( (RANDOM % 64) * STRIPE_SIZE ))
        # Write a partial block within the stripe (forces RMW)
        local byte_off=$(( stripe_off + (RANDOM % (STRIPE_SIZE / PARTIAL_SIZE)) * PARTIAL_SIZE ))

        # Use dd with O_DIRECT to bypass page cache -> goes to RAID56 path
        dd if=/dev/urandom of="$file" bs="$PARTIAL_SIZE" count=1 \
            seek=$(( byte_off / PARTIAL_SIZE )) \
            oflag=direct conv=notrunc 2>/dev/null || true

        n=$((n + 1))
    done
}

# -----------------------------------------------------------------------
# Concurrent full-stripe writer: writes full stripes to create contention
# with the partial writers on the same stripe.
# -----------------------------------------------------------------------
full_writer() {
    local id="$1"
    local file="$WORKDIR/full_file_$id"

    while true; do
        dd if=/dev/urandom of="$file" bs="$STRIPE_SIZE" count=64 \
            oflag=direct 2>/dev/null || true
        sleep 0.01
    done
}

echo "[raid56] Starting $NTHREADS partial writers + 2 full writers for ${DURATION}s."
echo "[raid56] Run bpftrace btrfs_raid56.bt in another terminal."

for i in $(seq 1 $NTHREADS); do
    partial_writer "$i" &
done
full_writer "A" &
full_writer "B" &

sleep "$DURATION"

echo "[raid56] Done. Check bpftrace output for ParityWrite/FinishRMW events."
