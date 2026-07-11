#!/usr/bin/env bash
# workloads/qgroup-race/workload.sh
# -----------------------------------------------------------------------
# Adversarial workload aimed squarely at the CVE-2025-39759 WINDOW, the one
# interleaving the hand-rolled qgroup workload and even the full xfstests
# -g qgroup group never entered (the witness probes reported "never entered"
# in every trace so far).
#
# The window (from BtrfsQgroupLifecycle.tla): inside btrfs_qgroup_rescan,
# after qgroup_rescan_init sets FLAG_RESCAN but before the ioctl reaches
# btrfs_qgroup_rescan queuing (rescan_running still FALSE), the code parks
# in btrfs_commit_transaction. If a concurrent btrfs_quota_disable samples
# rescan_running there, its wait_for_completion returns immediately and it
# proceeds to free the qgroup tree — colliding with the rescan's own
# zero_tracking OR (per the worker-race finding) with the worker the queuing
# then starts.
#
# Why the old workload missed it: it ran enable -> rescan -> disable
# SEQUENTIALLY in one thread, so disable never sampled while a rescan was
# mid-commit. Two levers change that here:
#
#   1. WIDEN the window — make btrfs_commit_transaction slow. A large,
#      heavily-fragmented metadata working set with continuous dirtying
#      means each commit writes many leaves, and the rescan scan itself
#      walks many leaves. Pre-fill + background churn do this.
#   2. Actually RACE — independent concurrent loops for rescan and disable
#      (rescan does NOT take subvol_sem, so it genuinely runs in parallel
#      with disable), plus an enabler to keep re-arming. Interleaving is
#      then driven by kernel timing, throwing thousands of darts at the
#      window instead of one fixed ordering.
#
# Run under the kprobe tracer (btrfs_qgroup.bt) + validate the trace:
#   PROBES=1 bash models/trace-validated/validate-trace.sh <trace> --fs <id>
# The cve_window / free_vs_iter probes flip to ENTERED if we hit it.
#
# Usage: bash workload.sh <mount> [duration_secs]
# -----------------------------------------------------------------------
set -uo pipefail

MOUNT="${1:?Usage: $0 <mount> [duration_secs]}"
DURATION="${2:-120}"
WORKDIR="$MOUNT/qgroup_race"
NSUBVOL="${NSUBVOL:-24}"
PREFILL_SECS="${PREFILL_SECS:-$((DURATION / 4))}"

PIDS=()
cleanup() {
    echo "[qgroup-race] cleaning up..."
    for p in "${PIDS[@]:-}"; do kill "$p" 2>/dev/null || true; done
    wait 2>/dev/null || true
    btrfs quota disable "$MOUNT" 2>/dev/null || true
    rm -rf "$WORKDIR" 2>/dev/null || true
}
trap cleanup EXIT

mkdir -p "$WORKDIR"

# -----------------------------------------------------------------------
# Phase 1: build a fat metadata working set — many subvolumes each with
# many small files. More leaves => slower commit => wider rescan window.
# -----------------------------------------------------------------------
echo "[qgroup-race] Phase 1: populating $NSUBVOL subvolumes (~${PREFILL_SECS}s)"
for i in $(seq 1 "$NSUBVOL"); do
    btrfs subvolume create "$WORKDIR/sv_$i" >/dev/null 2>&1 || true
done

prefill_end=$((SECONDS + PREFILL_SECS))
n=0
while [ $SECONDS -lt $prefill_end ]; do
    sv="$WORKDIR/sv_$(( (n % NSUBVOL) + 1 ))"
    d="$sv/d$((n % 64))"
    mkdir -p "$d" 2>/dev/null || true
    # small files: metadata-heavy, cheap data
    for j in $(seq 1 32); do
        printf '%0.sx' {1..64} > "$d/f_${n}_$j" 2>/dev/null || true
    done
    n=$((n + 1))
done
sync
echo "[qgroup-race] populated ~$((n * 32)) files"

# -----------------------------------------------------------------------
# Phase 2: background metadata churn — keeps transactions dirty so every
# commit (including the rescan's) has real work, holding the window open.
# -----------------------------------------------------------------------
churn() {
    local sv c=0
    while true; do
        sv="$WORKDIR/sv_$(( (RANDOM % NSUBVOL) + 1 ))"
        printf '%0.sy' {1..256} > "$sv/churn_$$_$c" 2>/dev/null || true
        rm -f "$sv/churn_$$_$((c - 50))" 2>/dev/null || true
        c=$((c + 1))
        [ $((c % 20)) -eq 0 ] && sync
    done
}
for _ in 1 2 3 4; do churn & PIDS+=($!); done

# snapshots force qgroup inheritance ops during the window
snapper() {
    local k=0
    while true; do
        btrfs subvolume snapshot "$WORKDIR/sv_1" "$WORKDIR/snap_$k" >/dev/null 2>&1 || true
        btrfs subvolume delete "$WORKDIR/snap_$k" >/dev/null 2>&1 || true
        k=$((k + 1))
    done
}
snapper & PIDS+=($!)

# -----------------------------------------------------------------------
# Phase 3: the race — independent concurrent loops. enable/disable serialize
# on subvol_sem; rescan runs free (the bug). Kernel timing decides the
# interleaving.
# -----------------------------------------------------------------------
echo "[qgroup-race] Phase 3: racing enable/rescan/disable for ${DURATION}s"
END=$((SECONDS + DURATION))

enabler()  { while [ $SECONDS -lt $END ]; do btrfs quota enable  "$MOUNT" 2>/dev/null || true; done; }
rescaner() { while [ $SECONDS -lt $END ]; do btrfs quota rescan  "$MOUNT" 2>/dev/null || true; done; }
waiter()   { while [ $SECONDS -lt $END ]; do btrfs quota rescan -w "$MOUNT" 2>/dev/null || true; done; }
disabler() { while [ $SECONDS -lt $END ]; do btrfs quota disable "$MOUNT" 2>/dev/null || true; done; }

enabler  & PIDS+=($!)
rescaner & PIDS+=($!)
rescaner & PIDS+=($!)
waiter   & PIDS+=($!)
disabler & PIDS+=($!)
disabler & PIDS+=($!)

# let the race run; cleanup trap stops everything
while [ $SECONDS -lt $END ]; do sleep 2; done
echo "[qgroup-race] race window closed"
