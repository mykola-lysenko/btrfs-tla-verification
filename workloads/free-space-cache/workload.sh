#!/usr/bin/env bash
# workloads/free-space-cache/workload.sh
# -----------------------------------------------------------------------
# Stress workload for BtrfsFreeSpaceCache.tla (NoDoubleAdd)
#
# Race window targeted:
#   btrfs_cache_block_group() loads the free space cache from disk.
#   If two threads both see BTRFS_CACHE_NO and both call
#   btrfs_add_free_space() for the same extent before either sets
#   BTRFS_CACHE_FINISHED, the same bytenr is added twice.
#
# What makes this tricky:
#   - The race requires a block group that is NOT yet cached (cold cache).
#   - We force cold cache by dropping the page cache between iterations.
#   - We use parallel allocation from multiple processes to maximize
#     the chance that two threads enter the caching path simultaneously.
#   - We alternate between large and small allocations to force the
#     allocator to search multiple block groups.
#   - We use nodatacow files to bypass the COW path and go directly
#     to the free space allocator.
#
# Expected trace events:
#   AddFreeSpace, RemoveFreeSpace, CacheBlockGroup_Start/Done
#   (from btrfs_free_space_cache.bt)
#   A VIOLATION_DoubleAdd event means the same bytenr was added twice.
#
# Invariant checked: NoDoubleAdd
#
# Usage:
#   mount -t btrfs /dev/sdb /mnt/btrfs
#   bash workload.sh /mnt/btrfs 60
# -----------------------------------------------------------------------

set -euo pipefail

MOUNT="${1:?Usage: $0 <mount> [duration_secs]}"
DURATION="${2:-60}"
WORKDIR="$MOUNT/fsc_stress"
NPROC=8

cleanup() {
    echo "[fsc] Cleaning up..."
    kill $(jobs -p) 2>/dev/null || true
    wait 2>/dev/null || true
    rm -rf "$WORKDIR" 2>/dev/null || true
}
trap cleanup EXIT

mkdir -p "$WORKDIR"

# -----------------------------------------------------------------------
# Phase 1: Populate the filesystem to create multiple block groups.
# Each block group has its own free space cache. We want many block
# groups so the allocator has to search across them.
# -----------------------------------------------------------------------
echo "[fsc] Phase 1: Populating filesystem to create multiple block groups..."
for i in $(seq 1 16); do
    # Create 64MB files to force new block group allocation
    dd if=/dev/zero of="$WORKDIR/bigfile_$i" bs=1M count=64 2>/dev/null || true
done
sync

# -----------------------------------------------------------------------
# Phase 2: Delete files to create free space in multiple block groups.
# This is the precondition: free extents scattered across block groups.
# -----------------------------------------------------------------------
echo "[fsc] Phase 2: Creating free space holes..."
for i in $(seq 1 2 16); do
    rm -f "$WORKDIR/bigfile_$i"
done
sync

# -----------------------------------------------------------------------
# Phase 3: Drop page cache to force cold free space cache reload.
# This is the key step: without this, the cache is already loaded and
# the race window doesn't exist.
# -----------------------------------------------------------------------
drop_cache() {
    echo 3 > /proc/sys/vm/drop_caches
}

# -----------------------------------------------------------------------
# Phase 4: Parallel allocation storm.
# Multiple processes allocate files simultaneously, all competing to
# load the same cold block group cache. This is the race window.
# -----------------------------------------------------------------------
allocator() {
    local id="$1"
    local dir="$WORKDIR/alloc_$id"
    mkdir -p "$dir"
    local n=0
    while true; do
        # Vary sizes: small (4KB) and medium (256KB) to hit different
        # free space entries in the cache
        local size=$((4 * (RANDOM % 64 + 1)))
        dd if=/dev/zero of="$dir/f_$n" bs=1K count="$size" 2>/dev/null || true
        n=$((n + 1))
        # Delete every 10th file to keep free space available
        if [ $((n % 10)) -eq 0 ]; then
            rm -f "$dir/f_$((n - 10))" 2>/dev/null || true
        fi
    done
}

echo "[fsc] Phase 4: Starting $NPROC parallel allocators for ${DURATION}s."
echo "[fsc] Run bpftrace btrfs_free_space_cache.bt in another terminal."

for i in $(seq 1 $NPROC); do
    allocator "$i" &
done

# Periodically drop cache to repeatedly force cold-cache reload
END=$((SECONDS + DURATION))
DROPS=0
while [ $SECONDS -lt $END ]; do
    sleep 3
    drop_cache
    DROPS=$((DROPS + 1))
    echo "[fsc] Cache drop #$DROPS (forces cold free space cache reload)"
done

echo "[fsc] Done. $DROPS cache drops. Check bpftrace output for AddFreeSpace events."
