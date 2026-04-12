#!/usr/bin/env bash
# workloads/autodefrag/workload.sh
# -----------------------------------------------------------------------
# Stress workload for BtrfsAutodefrag.tla (NoStaleDefrag)
#
# Race window targeted:
#   The autodefrag worker maintains a list of inodes to defragment.
#   If an inode is deleted between when it was added to the defrag list
#   and when the worker processes it, the worker operates on a stale
#   (freed) inode — a use-after-free.
#
# What makes this tricky:
#   - The autodefrag worker runs asynchronously on a workqueue.
#   - The window between "inode added to defrag list" and "worker runs"
#     can be hundreds of milliseconds.
#   - We maximize this window by:
#     1. Mounting with autodefrag enabled
#     2. Writing fragmented files (many small writes to trigger autodefrag)
#     3. Immediately deleting files after writing (races with the worker)
#     4. Recreating files with the same name (forces inode reuse)
#   - Inode reuse is the key: if the worker gets an old inode number
#     that has been reused for a new file, it defragments the wrong file.
#
# Mount option required: -o autodefrag
#
# Expected trace events:
#   DefragFile_Enter/Done, EvictInode, InodeGet
#   VIOLATION_StaleDefrag or VIOLATION_EvictDuringDefrag -> bug detected
#
# Invariant checked: NoStaleDefrag
#
# Usage:
#   mount -t btrfs -o autodefrag /dev/sdb /mnt/btrfs
#   bash workload.sh /mnt/btrfs 120
# -----------------------------------------------------------------------

set -euo pipefail

MOUNT="${1:?Usage: $0 <mount> [duration_secs]}"
DURATION="${2:-120}"
WORKDIR="$MOUNT/autodefrag_stress"
NPROC=8

cleanup() {
    echo "[autodefrag] Cleaning up..."
    kill $(jobs -p) 2>/dev/null || true
    wait 2>/dev/null || true
    rm -rf "$WORKDIR" 2>/dev/null || true
}
trap cleanup EXIT

# Verify autodefrag is enabled
if ! mount | grep "$MOUNT" | grep -q autodefrag; then
    echo "[autodefrag] WARNING: $MOUNT is not mounted with -o autodefrag"
    echo "[autodefrag] Remount with: mount -o remount,autodefrag $MOUNT"
fi

mkdir -p "$WORKDIR"

# -----------------------------------------------------------------------
# Fragmented writer: writes many small random writes to the same file.
# This is the pattern that triggers autodefrag: many small extents.
# -----------------------------------------------------------------------
fragmented_writer() {
    local id="$1"
    local dir="$WORKDIR/worker_$id"
    mkdir -p "$dir"

    while true; do
        local file="$dir/frag_file"

        # Write 256 small random chunks to create a fragmented file
        for i in $(seq 1 256); do
            dd if=/dev/urandom of="$file" bs=512 count=1 \
                seek=$((RANDOM % 256)) conv=notrunc 2>/dev/null || true
        done
        sync

        # Immediately delete — races with the autodefrag worker
        rm -f "$file"

        # Recreate with the same name — forces inode number reuse
        # (Btrfs may reuse the same inode number for the new file)
        dd if=/dev/zero of="$file" bs=4096 count=1 2>/dev/null || true
    done
}

# -----------------------------------------------------------------------
# Rapid create/delete: creates and deletes many files rapidly.
# This maximizes inode churn and the chance of inode number reuse.
# -----------------------------------------------------------------------
inode_churner() {
    local id="$1"
    local dir="$WORKDIR/churn_$id"
    mkdir -p "$dir"
    local n=0

    while true; do
        # Create 100 files
        for i in $(seq 1 100); do
            dd if=/dev/urandom of="$dir/f_$i" bs=512 count=$((RANDOM % 8 + 1)) \
                2>/dev/null || true
        done
        # Delete them all immediately
        rm -f "$dir"/f_* 2>/dev/null || true
        n=$((n + 1))
    done
}

echo "[autodefrag] Starting $NPROC fragmented writers + $NPROC inode churners for ${DURATION}s."
echo "[autodefrag] Run bpftrace btrfs_autodefrag.bt in another terminal."

for i in $(seq 1 $NPROC); do
    fragmented_writer "$i" &
    inode_churner "$i" &
done

sleep "$DURATION"

echo "[autodefrag] Done. Check bpftrace output for DefragFile/EvictInode events."
