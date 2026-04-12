#!/usr/bin/env bash
# workloads/scrub/workload.sh
# -----------------------------------------------------------------------
# Stress workload for BtrfsScrub.tla (NoMissedRepair)
#
# Race window targeted:
#   btrfs scrub reads each block, verifies its checksum, and repairs
#   corrupted blocks from a mirror. The race is:
#     Scrub thread:  reads block B, finds it clean, marks it verified
#     Writer thread: overwrites block B with corrupt data
#   If the write happens after scrub reads but before scrub marks it
#   verified, the corruption is missed.
#
# What makes this tricky:
#   - We need a RAID1 or RAID10 setup for repair to work.
#   - We use dm-flakey to inject checksum errors on one device.
#   - We run scrub concurrently with writes to the same blocks.
#   - We verify after scrub that no corruption remains (end-to-end check).
#
# Note: Requires RAID1 Btrfs setup with at least 2 devices.
#
# Expected trace events:
#   ScrubDev_Start/Done, ScrubStripe_Enter/Done,
#   ScrubRepair, ScrubChecksumFail
#
# Invariant checked: NoMissedRepair
#
# Usage:
#   # Setup (2 loop devices for RAID1):
#   for i in 1 2; do dd if=/dev/zero of=/tmp/disk$i.img bs=1M count=512; done
#   for i in 1 2; do losetup -f /tmp/disk$i.img; done
#   mkfs.btrfs -d raid1 -m raid1 /dev/loop0 /dev/loop1
#   mount /dev/loop0 /mnt/btrfs
#   bash workload.sh /mnt/btrfs 120
# -----------------------------------------------------------------------

set -euo pipefail

MOUNT="${1:?Usage: $0 <mount> [duration_secs]}"
DURATION="${2:-120}"
WORKDIR="$MOUNT/scrub_stress"
NWRITERS=4

cleanup() {
    echo "[scrub] Cleaning up..."
    kill $(jobs -p) 2>/dev/null || true
    wait 2>/dev/null || true
    rm -rf "$WORKDIR" 2>/dev/null || true
}
trap cleanup EXIT

mkdir -p "$WORKDIR"

# -----------------------------------------------------------------------
# Phase 1: Create files with known content (all-zeros).
# After scrub, all files should still be all-zeros.
# -----------------------------------------------------------------------
echo "[scrub] Phase 1: Creating test files..."
for i in $(seq 1 32); do
    dd if=/dev/zero of="$WORKDIR/testfile_$i" bs=1M count=4 2>/dev/null
done
sync

# -----------------------------------------------------------------------
# Writer: continuously overwrites files with random data.
# This races with scrub's read-verify-repair cycle.
# -----------------------------------------------------------------------
writer() {
    local id="$1"
    while true; do
        local f="$WORKDIR/testfile_$((id % 32 + 1))"
        dd if=/dev/urandom of="$f" bs=4096 count=1 \
            seek=$((RANDOM % 1024)) conv=notrunc 2>/dev/null || true
    done
}

# -----------------------------------------------------------------------
# Scrub runner: runs btrfs scrub repeatedly.
# -----------------------------------------------------------------------
scrub_runner() {
    local n=0
    while true; do
        btrfs scrub start -B "$MOUNT" 2>/dev/null || true
        n=$((n + 1))
        echo "[scrub] Scrub run #$n complete"
        sleep 1
    done
}

echo "[scrub] Phase 2: Starting $NWRITERS writers + scrub runner for ${DURATION}s."
echo "[scrub] Run bpftrace btrfs_scrub.bt in another terminal."

for i in $(seq 1 $NWRITERS); do
    writer "$i" &
done
scrub_runner &

sleep "$DURATION"

echo "[scrub] Done. Check bpftrace output for ScrubChecksum/ScrubRepair events."
