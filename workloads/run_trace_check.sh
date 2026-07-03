#!/usr/bin/env bash
# workloads/run_trace_check.sh
# -----------------------------------------------------------------------
# Harness: run a workload + bpftrace script + invariant checker together.
#
# This script:
#   1. Starts the bpftrace script in the background (writes JSON to /tmp)
#   2. After the run, time-sorts the trace and runs the invariant checker
#      on it post-hoc (inline checking cannot keep up with event rates)
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
# BPFTRACE_DIR can be overridden, e.g. to use the tracepoint-based edition:
#   BPFTRACE_DIR=$REPO_DIR/tracing/bpftrace-tp
BPFTRACE_DIR="${BPFTRACE_DIR:-$REPO_DIR/tracing/bpftrace}"
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

echo "============================================================"
echo " Btrfs Trace Conformance Check"
echo "============================================================"
echo " Subsystem : $SUBSYSTEM"
echo " Mount     : $MOUNT"
echo " Duration  : ${DURATION}s"
echo " Trace     : $TRACE_FILE"
echo " Report    : $REPORT_FILE"
echo "============================================================"

# -----------------------------------------------------------------------
# Start bpftrace — writes JSON events to a local temp file
# -----------------------------------------------------------------------
echo "[harness] Starting bpftrace: ${BT_SCRIPT[$SUBSYSTEM]}"
# The checker deliberately runs POST-HOC on the saved trace, not inline on
# a FIFO: a Python checker parses ~50k JSON lines/s while lock-heavy probes
# emit >100k events/s — inline checking backpressures bpftrace's stdout and
# silently drops events, corrupting the very state the checker tracks.
#
# -B line: bpftrace fully buffers stdout when piped; line-buffer it so
# nothing is lost when we stop it.
# Large perf ring buffer: high-frequency probes (tree locks) overflow the
# default 64 pages/cpu and drop events. stderr goes to bpftrace.log
# ("Lost N events" warnings, attach errors).
# The live trace is written to tmpfs (/dev/shm) first: when the results dir
# — or even /tmp — is on a slow filesystem (9p share under QEMU: ~12 MB/s),
# writing the JSON firehose there stalls bpftrace's output pipe and drops
# millions of events. /dev/shm is guaranteed RAM-backed.
export BPFTRACE_PERF_RB_PAGES="${BPFTRACE_PERF_RB_PAGES:-2048}"
TRACE_TMP_DIR="/dev/shm"
[[ -d "$TRACE_TMP_DIR" && -w "$TRACE_TMP_DIR" ]] || TRACE_TMP_DIR="/tmp"
TRACE_TMP="$(mktemp "$TRACE_TMP_DIR/btrfs_trace.XXXXXX.jsonl")"
bpftrace -B line "$BT_FILE" > "$TRACE_TMP" 2>"$OUT_DIR/bpftrace.log" &
BT_PID=$!

# Wait for bpftrace to attach (BEGIN block writes a "# ... started" banner).
# On debug kernels (lockdep, BTF) startup can take ~10s; don't start the
# workload before probes are live or early events are silently missed.
for _ in $(seq 1 60); do
    [[ -s "$TRACE_TMP" ]] && break
    sleep 1
done
if [[ ! -s "$TRACE_TMP" ]]; then
    echo "[harness] WARNING: bpftrace produced no output after 60s — probes may not be attached"
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
# Stop bpftrace, then run the checker post-hoc on the saved trace
# -----------------------------------------------------------------------
echo "[harness] Workload complete. Stopping bpftrace..."
# SIGINT lets bpftrace detach probes, run its END block, and flush.
kill -INT "$BT_PID" 2>/dev/null || true
for _ in $(seq 1 15); do
    kill -0 "$BT_PID" 2>/dev/null || break
    sleep 1
done
kill "$BT_PID" 2>/dev/null || true
wait "$BT_PID" 2>/dev/null || true

# Sort by timestamp: bpftrace merges per-CPU perf buffers in poll order,
# so cross-CPU events can appear out of order, which breaks stateful
# checkers (a Release can appear before its Acquire).
python3 - "$TRACE_TMP" <<'PYSORT' || true
import json, sys
path = sys.argv[1]
lines = open(path, errors="replace").readlines()
def key(line):
    try:
        return json.loads(line).get("ts", 0)
    except Exception:
        return 0
lines.sort(key=key)
open(path, "w").writelines(lines)
PYSORT

CHECKER_EXIT=0
if [[ -n "${CHECKER[$SUBSYSTEM]+x}" ]] && [[ -f "$CHECKER_DIR/${CHECKER[$SUBSYSTEM]}" ]]; then
    echo "[harness] Running checker: ${CHECKER[$SUBSYSTEM]}"
    python3 "$CHECKER_DIR/${CHECKER[$SUBSYSTEM]}" < "$TRACE_TMP" > "$REPORT_FILE" 2>&1 \
        || CHECKER_EXIT=$?
else
    echo "[harness] No Python checker for $SUBSYSTEM — inline VIOLATION_ events will appear in trace."
fi

# Move the trace from tmpfs to the results dir (mktemp files are 0600)
cp "$TRACE_TMP" "$TRACE_FILE" && rm -f "$TRACE_TMP"
chmod 644 "$TRACE_FILE" "$REPORT_FILE" "$OUT_DIR/bpftrace.log" 2>/dev/null || true

# -----------------------------------------------------------------------
# Report
# -----------------------------------------------------------------------
echo ""
echo "============================================================"
echo " Results for: $SUBSYSTEM"
echo "============================================================"
VIOLATION_COUNT=$(grep -c "VIOLATION" "$TRACE_FILE" 2>/dev/null) || VIOLATION_COUNT=0
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
