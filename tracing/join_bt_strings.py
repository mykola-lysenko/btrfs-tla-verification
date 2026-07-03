#!/usr/bin/env python3
"""Join adjacent string literals in bpftrace scripts.

The scripts in tracing/bpftrace*/ were written with C-style adjacent string
literal concatenation inside printf(), e.g.:

    printf("{\"tid\":%d,"
           "\"ts\":%llu}\n", tid, nsecs);

bpftrace's grammar (all versions through at least 0.26) does not support
this — it is a syntax error. This tool rewrites each script so that string
literals separated only by whitespace are merged into a single literal.

Usage: python3 join_bt_strings.py <file-or-dir>...   (rewrites in place)
"""
import re
import sys
from pathlib import Path

# Two string literals separated only by whitespace (incl. newlines).
# Handles escaped characters inside literals.
ADJACENT = re.compile(r'"((?:[^"\\]|\\.)*)"\s*\n\s*"((?:[^"\\]|\\.)*)"')


def join_strings(text: str) -> str:
    prev = None
    while prev != text:
        prev = text
        text = ADJACENT.sub(lambda m: '"' + m.group(1) + m.group(2) + '"', text)
    return text


def main(argv):
    changed = 0
    for arg in argv:
        p = Path(arg)
        files = sorted(p.rglob("*.bt")) if p.is_dir() else [p]
        for f in files:
            orig = f.read_text()
            new = join_strings(orig)
            if new != orig:
                f.write_text(new)
                print(f"rewrote {f}")
                changed += 1
    print(f"{changed} file(s) changed")


if __name__ == "__main__":
    main(sys.argv[1:] or ["."])
