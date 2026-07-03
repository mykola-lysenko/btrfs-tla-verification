#!/usr/bin/env python3
"""Audit tracing/bpftrace-tp scripts against a kernel's tracepoint formats.

Tracepoint names and fields are NOT a stable ABI — several were renamed
between 6.9 and 7.1 (qgroup_* -> btrfs_qgroup_*, find_free_extent ->
btrfs_find_free_extent, ...) and field sets changed. Run this audit whenever
the target kernel changes.

Inputs:
  1. A formats dump produced in the guest by:
       for d in /sys/kernel/tracing/events/btrfs/*/; do
         echo "=== $(basename $d) ==="; grep field: $d/format
       done > qemu/tp-formats.txt
  2. The .bt scripts in tracing/bpftrace-tp/.

Reports every probe whose tracepoint is missing or whose args-> field
accesses don't exist in the format. Exit code 1 if any problem found.

Usage: python3 tracing/audit_tp_fields.py [formats.txt] [scripts-dir]
"""
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def parse_formats(path):
    fmt, cur = {}, None
    for line in open(path):
        m = re.match(r"=== (\w+) ===", line)
        if m:
            cur = m.group(1)
            fmt[cur] = set()
            continue
        m = re.search(r"field:.*?(\w+)(\[\d*\])?;", line)
        if m and cur:
            fmt[cur].add(m.group(1))
    return fmt


def main():
    formats = Path(sys.argv[1]) if len(sys.argv) > 1 else REPO / "qemu/tp-formats.txt"
    scripts = Path(sys.argv[2]) if len(sys.argv) > 2 else REPO / "tracing/bpftrace-tp"
    fmt = parse_formats(formats)
    bad = 0
    for f in sorted(scripts.glob("*.bt")):
        text = f.read_text()
        for p in re.finditer(r"((?:tracepoint:btrfs:\w+\s*,?\s*)+)\{", text):
            names = re.findall(r"tracepoint:btrfs:(\w+)", p.group(1))
            i = p.end() - 1
            depth = 0
            for j in range(i, len(text)):
                if text[j] == "{":
                    depth += 1
                elif text[j] == "}":
                    depth -= 1
                    if depth == 0:
                        break
            used = set(re.findall(r"args->(\w+)", text[i:j]))
            for n in names:
                if n not in fmt:
                    print(f"{f.name}: {n}: TRACEPOINT MISSING")
                    bad += 1
                elif used - fmt[n]:
                    avail = sorted(x for x in fmt[n] if not x.startswith("common_"))
                    print(f"{f.name}: {n}: bad fields {sorted(used - fmt[n])}; available: {avail}")
                    bad += 1
    print(f"--- {bad} problem(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
