#!/usr/bin/env bash
# workloads/run_trace_check.sh
# -----------------------------------------------------------------------
# Harness: run a workload + bpftrace script + invariant checker together.
#
# This script:
#   1. Starts the bpftrace script in the background (writes JSON to a FIFO)
#   2. Starts the invariant checker in the background (reads from FIFO)
#   3. Runs the workload in the foreground
#   4. Stops bpftrace and waits for the checker to finish
#   5. Reports the conformance result
#
# Usage:
#   sudo bash run_trace_check.sh <subsystem> <mount> [duration_secs]
#
# Examples:
#   sudo bash run_trace_check.sh extent-buffer-lock /mnt/btrfs 60
#   sudo bash run_trace_check.sh qgroup             /mnt/btrfs 60
#   sudo bash run_trace_check.sh fsync-log-tree     /mnt/btrfs 120
#   sudo bash run_trace_check.sh transaction-chain  /mnt/btrfs 120
#   sudo bash run_trace_check.sh free-space-cache   /mnt/btrfs 60
#   sudo bash run_trace_check.sh space-reservation  /mnt/btrfs 120
#   sudo bash run_trace_check.sh snapshot-creation  /mnt/btrfs 120
#   sudo bash run_trace_check.sh balance-relocation /mnt/btrfs 180
#   sudo bash run_trace_check.sh send-receive       /mnt/btrfs 120
#   sudo bash run_trace_check.sh cow-path           /mnt/btrfs 120
#   sudo bash run_trace_check.sh raid56             /mnt/btrfs 120
#   sudo bash run_trace_check.sh scrub              /mnt/btrfs 120
#   sudo bash run_trace_check.sh autodefrag         /mnt/btrfs 120
#
# Requirements:
#   - bpftrace >= 0.14 with CAP_SYS_ADMIN
#   - Python >= 3.10
#   - Btrfs mounted at <mount> with CONFIG_DEBUG_INFO_BTF=y
#   - Run as root (for bpftrace kprobes)
# -----------------------------------------------------------------------

set -euo pipefail

SUBSYSTEM="${1:?Usage: $0 <subsystem> <mount> [duration_secs]}"
MOUNT="${2:?Usage: $0 <subsystem> <mount> [duration_secs]}"
DURATION="${3:-60}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(dirname "$SCRIPT_DIR")"
BPFTRACE_DIR="$REPO_DIR/tracing/bpftrace"
CHECKER_DIR="$REPO_DIR/tracing/checkers"
WORKLOAD_DIR="$SCRIPT_DIR/$SUBSYSTEM"

# Map subsystem name to bpftrace script and checker
declare -A BT_SCRIPT=(
    [extent-buffer-lock]="btrfs_extent_buffer_lock.bt"
    [free-space-cache]="btrfs_free_space_cache.bt"
    [qgroup]="btrfs_qgroup.bt"
    [fsync-log-tree]="btrfs_fsync_log_tree.bt"
    [transaction-chain]="btrfs_transaction_chain.bt"
    [send-receive]="btrfs_send_receive.bt"
    [raid56]="btrfs_raid56.bt"
    [scrub]="btrfs_scrub.bt"
    [space-reservation]="btrfs_space_reservation.bt"
    [balance-relocation]="btrfs_balance_relocation.bt"
    [snapshot-creation]="btrfs_snapshot_creation.bt"
    [autodefrag]="btrfs_autodefrag.bt"
    [compression]="btrfs_compression.bt"
    [cow-path]="btrfs_cow_path.bt"
    [async-discard]="btrfs_async_discard.bt"
    [dev-replace]="btrfs_dev_replace.bt"
)

declare -A CHECKER=(
    [extent-buffer-lock]="btrfs_extent_buffer_lock_checker.py"
    [free-space-cache]="btrfs_free_space_cache_checker.py"
    [qgroup]="btrfs_qgroup_checker.py"
    [fsync-log-tree]="btrfs_fsync_log_tree_checker.py"
    [transaction-chain]="btrfs_transaction_chain_checker.py"
)

declare -A WORKLOAD_CMD=(
    [extent-buffer-lock]="python3 $WORKLOAD_DIR/workload.py --mount $MOUNT --threads 16 --duration $DURATION"
    [free-space-cache]="bash $WORKLOAD_DIR/workload.sh $MOUNT $DURATION"
    [qgroup]="bash $WORKLOAD_DIR/workload.sh $MOUNT $DURATION"
    [fsync-log-tree]="python3 $WORKLOAD_DIR/workload.py --mount $MOUNT --duration $DURATION"
    [transaction-chain]="python3 $WORKLOAD_DIR/workload.py --mount $MOUNT --threads 32 --duration $DURATION"
    [send-receive]="bash $WORKLOAD_DIR/workload.sh $MOUNT $DURATION"
    [raid56]="bash $WORKLOAD_DIR/workload.sh $MOUNT $DURATION"
    [scrub]="bash $WORKLOAD_DIR/workload.sh $MOUNT $DURATION"
    [space-reservation]="python3 $WORKLOAD_DIR/workload.py --mount $MOUNT --duration $DURATION"
    [balance-relocation]="bash $WORKLOAD_DIR/workload.sh $MOUNT $DURATION"
    [snapshot-creation]="python3 $WORKLOAD_DIR/workload.py --mount $MOUNT --duration $DURATION"
    [autodefrag]="bash $WORKLOAD_DIR/workload.sh $MOUNT $DURATION"
    [cow-path]="bash $WORKLOAD_DIR/workload.sh $MOUNT $DURATION"
)

# Validate subsystem
if [[ -z "${BT_SCRIPT[$SUBSYSTEM]+x}" ]]; then
    echo "ERROR: Unknown subsystem '$SUBSYSTEM'"
    echo "Available: ${!BT_SCRIPT[*]}"
    exit 1
fi

BT_FILE="$BPFTRACE_DIR/${BT_SCRIPT[$SUBSYSTEM]}"
if [[ ! -f "$BT_FILE" ]]; then
    echo "ERROR: bpftrace script not found: $BT_FILE"
    exit 1
fi

# Create output directory
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUT_DIR="$SCRIPT_DIR/results/${SUBSYSTEM}_${TIMESTAMP}"
mkdir -p "$OUT_DIR"
TRACE_FILE="$OUT_DIR/trace.jsonl"
REPORT_FILE="$OUT_DIR/report.txt"
FIFO="$OUT_DIR/trace.fifo"

echo "============================================================"
echo " Btrfs Trace Conformance Check"
echo "============================================================"
echo " Subsystem : $SUBSYSTEM"
echo " Mount     : $MOUNT"
echo " Duration  : ${DURATION}s"
echo " Trace     : $TRACE_FILE"
echo " Report    : $REPORT_FILE"
echo "============================================================"

# Create FIFO for streaming trace to checker
mkfifo "$FIFO"

# -----------------------------------------------------------------------
# Start bpftrace — writes JSON events to FIFO and trace file
# -----------------------------------------------------------------------
echo "[harness] Starting bpftrace: ${BT_SCRIPT[$SUBSYSTEM]}"
bpftrace "$BT_FILE" | tee "$TRACE_FILE" > "$FIFO" &
BT_PID=$!

# Give bpftrace time to attach probes
sleep 2

# -----------------------------------------------------------------------
# Start checker — reads from FIFO
# -----------------------------------------------------------------------
CHECKER_FILE="${CHECKER[$SUBSYSTEM]+x}"
if [[ -n "${CHECKER[$SUBSYSTEM]+x}" ]] && [[ -f "$CHECKER_DIR/${CHECKER[$SUBSYSTEM]}" ]]; then
    echo "[harness] Starting checker: ${CHECKER[$SUBSYSTEM]}"
    python3 "$CHECKER_DIR/${CHECKER[$SUBSYSTEM]}" < "$FIFO" > "$REPORT_FILE" 2>&1 &
    CHECKER_PID=$!
else
    echo "[harness] No Python checker for $SUBSYSTEM — inline VIOLATION_ events will appear in trace."
    # Drain FIFO so bpftrace doesn't block
    cat "$FIFO" > /dev/null &
    CHECKER_PID=$!
fi

# -----------------------------------------------------------------------
# Run workload
# -----------------------------------------------------------------------
echo "[harness] Starting workload..."
WORKLOAD="${WORKLOAD_CMD[$SUBSYSTEM]+x}"
if [[ -n "${WORKLOAD_CMD[$SUBSYSTEM]+x}" ]]; then
    eval "${WORKLOAD_CMD[$SUBSYSTEM]}" || true
else
    echo "[harness] No workload defined for $SUBSYSTEM — running for ${DURATION}s..."
    sleep "$DURATION"
fi

# -----------------------------------------------------------------------
# Stop bpftrace and wait for checker
# -----------------------------------------------------------------------
echo "[harness] Workload complete. Stopping bpftrace..."
kill "$BT_PID" 2>/dev/null || true
wait "$BT_PID" 2>/dev/null || true

# Close FIFO so checker sees EOF
exec 3>"$FIFO" && exec 3>&-  # open and immediately close write end
wait "$CHECKER_PID" 2>/dev/null || true
CHECKER_EXIT=$?

# -----------------------------------------------------------------------
# Report
# -----------------------------------------------------------------------
echo ""
echo "============================================================"
echo " Results for: $SUBSYSTEM"
echo "============================================================"
VIOLATION_COUNT=$(grep -c "VIOLATION" "$TRACE_FILE" 2>/dev/null || echo 0)
echo " Trace events  : $(wc -l < "$TRACE_FILE") lines"
echo " Violations    : $VIOLATION_COUNT inline VIOLATION_ events"

if [[ -f "$REPORT_FILE" ]]; then
    echo ""
    echo " Checker output:"
    cat "$REPORT_FILE"
fi

echo ""
if [[ $CHECKER_EXIT -eq 0 && $VIOLATION_COUNT -eq 0 ]]; then
    echo " RESULT: CONFORMS — no invariant violations detected"
elif [[ $CHECKER_EXIT -ne 0 || $VIOLATION_COUNT -gt 0 ]]; then
    echo " RESULT: VIOLATIONS DETECTED — see $REPORT_FILE and $TRACE_FILE"
fi
echo "============================================================"
echo " Full trace saved to: $TRACE_FILE"
echo "============================================================"

exit $CHECKER_EXIT
