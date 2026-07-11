#!/usr/bin/env bash
# mutation-test.sh — negative validation of BtrfsQgroupLifecycle.
#
# Generates guaranteed-illegal mutants of a real trace (tracing/mutate_trace.py)
# and checks that TLC REJECTS every one of them. A surviving mutant means the
# model is too permissive (it accepts an ordering the kernel cannot produce),
# which would make "TRACE ACCEPTED" on the real trace close to vacuous.
# Unmutated truncated prefixes run as controls and must be ACCEPTED.
#
# Usage:
#   bash mutation-test.sh <trace.jsonl> [per_op]
set -uo pipefail

TRACE="${1:?usage: mutation-test.sh <trace.jsonl> [per_op]}"
PER_OP="${2:-6}"
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(dirname "$(dirname "$DIR")")"
MUTDIR="$(mktemp -d)"

python3 "$REPO/tracing/mutate_trace.py" "$TRACE" -o "$MUTDIR" --per-op "$PER_OP"
echo

pass=0; fail=0
printf '%-22s %-8s %-44s %s\n' "mutant" "expect" "result" "verdict"
while IFS=$'\t' read -r name op expect diverge_by n_events detail; do
    [ "$name" = "name" ] && continue
    out="$(DIAG=0 bash "$DIR/validate-trace.sh" "$MUTDIR/$name.jsonl" 2>&1)"
    rc=$?
    result="$(printf '%s\n' "$out" | grep '^RESULT:' | sed 's/^RESULT: //' | cut -c1-44)"
    if [ "$expect" = "ACCEPT" ]; then
        verdict=$([ "$rc" -eq 0 ] && echo PASS || echo "FAIL (control not accepted!)")
    else
        case "$rc" in
            1) verdict="PASS (killed)";;
            0) verdict="FAIL — SURVIVED: $detail";;
            *) verdict="ERROR (rc=$rc): $detail";;
        esac
    fi
    case "$verdict" in PASS*) pass=$((pass+1));; *) fail=$((fail+1));; esac
    printf '%-22s %-8s %-44s %s\n' "$name" "$expect" "$result" "$verdict"
done < "$MUTDIR/manifest.tsv"

echo
if [ "$fail" -eq 0 ]; then
    echo "MUTATION RESULT: $pass/$pass passed — model rejects all illegal orderings"
    rm -rf "$MUTDIR"
    exit 0
else
    echo "MUTATION RESULT: $fail FAILURES of $((pass+fail)) — see $MUTDIR/manifest.tsv"
    echo "  (mutants kept in $MUTDIR for inspection)"
    exit 1
fi
