#!/usr/bin/env bash
# workloads/cow-path/workload.sh
# -----------------------------------------------------------------------
# Stress workload for BtrfsCOWPath.tla (NoUAF, CVE-2023-1611)
#
# Race window targeted:
#   btrfs_search_slot() COWs a path from root to leaf.
#   If another thread frees an extent buffer that is on the COW path
#   (e.g., via btrfs_free_tree_block) while the first thread is
#   mid-COW, the first thread accesses freed memory.
#
# What makes this tricky:
#   - The race requires a tree modification (COW) concurrent with a
#     tree block free. This happens during:
#     1. Snapshot deletion: frees many tree blocks rapidly
#     2. Balance: relocates tree blocks (frees old, allocates new)
#     3. Truncation: frees extent tree blocks
#   - We combine all three to maximize the chance of hitting the window.
#   - We use many concurrent writers to keep the COW path busy.
#
# Expected trace events:
#   COWPath_Enter/Done, FreeTreeBlock, ExtentBufferRef
#   VIOLATION_UAF -> bug detected
#
# Invariant checked: NoUAF
#
# Usage:
#   mount -t btrfs /dev/sdb /mnt/btrfs
#   bash workload.sh /mnt/btrfs 120
# -----------------------------------------------------------------------

set -euo pipefail

MOUNT="${1:?Usage: $0 <mount> [duration_secs]}"
DURATION="${2:-120}"
WORKDIR="$MOUNT/cow_stress"
NPROC=8

cleanup() {
    echo "[cow] Cleaning up..."
    kill $(jobs -p) 2>/dev/null || true
    wait 2>/dev/null || true
    # Delete all test subvolumes
    for sv in "$WORKDIR"/subvol_* "$WORKDIR"/snap_*; do
        btrfs subvolume delete "$sv" 2>/dev/null || true
    done
    rm -rf "$WORKDIR" 2>/dev/null || true
}
trap cleanup EXIT

mkdir -p "$WORKDIR"

# -----------------------------------------------------------------------
# Setup: create subvolumes with many files to build deep B-trees
# -----------------------------------------------------------------------
echo "[cow] Setup: creating subvolumes..."
for i in $(seq 1 4); do
    btrfs subvolume create "$WORKDIR/subvol_$i"
    for j in $(seq 1 500); do
        dd if=/dev/urandom of="$WORKDIR/subvol_$i/f_$j" bs=4096 count=4 2>/dev/null
    done
done
sync

# -----------------------------------------------------------------------
# Writer: continuously writes to files (keeps COW path busy)
# -----------------------------------------------------------------------
writer() {
    local sv="$1"
    while true; do
        local f="$sv/f_$((RANDOM % 500 + 1))"
        dd if=/dev/urandom of="$f" bs=4096 count=1 conv=notrunc 2>/dev/null || true
    done
}

# -----------------------------------------------------------------------
# Snapshot creator/deleter: rapidly creates and deletes snapshots.
# Snapshot deletion frees many tree blocks, racing with the COW path.
# -----------------------------------------------------------------------
snap_worker() {
    local sv="$1"
    local n=0
    while true; do
        local snap="$WORKDIR/snap_${sv##*/}_$n"
        btrfs subvolume snapshot "$sv" "$snap" 2>/dev/null || true
        sleep 0.05
        btrfs subvolume delete "$snap" 2>/dev/null || true
        n=$((n + 1))
    done
}

# -----------------------------------------------------------------------
# Truncator: truncates files to zero and rewrites them.
# Truncation frees extent tree blocks, racing with the COW path.
# -----------------------------------------------------------------------
truncator() {
    local sv="$1"
    while true; do
        local f="$sv/f_$((RANDOM % 500 + 1))"
        truncate -s 0 "$f" 2>/dev/null || true
        dd if=/dev/urandom of="$f" bs=4096 count=$((RANDOM % 16 + 1)) 2>/dev/null || true
    done
}

echo "[cow] Starting writers, snapshot workers, and truncators for ${DURATION}s."
echo "[cow] Run bpftrace btrfs_cow_path.bt in another terminal."

for i in $(seq 1 4); do
    writer "$WORKDIR/subvol_$i" &
    snap_worker "$WORKDIR/subvol_$i" &
    truncator "$WORKDIR/subvol_$i" &
done

sleep "$DURATION"

echo "[cow] Done. Check bpftrace output for COWPath/FreeTreeBlock events."
