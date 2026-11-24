#!/usr/bin/env python3
"""How much of a check is theorem proofs, and how much is everything else
(SW-4715, docs/proposals/parallel-checking.md, "After proof irrelevance").

Reads a per-declaration time table (the `decls.csv` that
docs/reviews/SW-4608/parse_timings.py writes from `check --no-cache
--timings=all`: decl, elab_ms, kernel_ms, total_ms, ...) and the project's
sources, and splits the time into
  - theorems: a declaration whose name, or whose owner's name (for a helper
    lifted from it, `Ns.thm.%match1`, or a local definition `Ns.thm.go`), is
    declared with `theorem` in the namespace the name starts with;
  - the rest: definitions, types, instances, tests, generated declarations.
A theorem's time includes elaborating its statement, which the table does
not separate, so "the rest" is a lower bound on what a statements-first pass
must do, and "theorems" an upper bound on what it leaves out. Names are
matched from text: a `theorem` inside a comment counts, and a definition and
a theorem with one name in one namespace both count as the theorem. A
group checked together (`a, b, c` in the table) is classed by its first
member. A file with no `namespace` line (the standard library's) gives its
theorems by short name only, and a declaration outside every project
namespace is a theorem if any part of its name is one of those: looser, so
pass the library's folder only when its share matters.

With a units table as well (unit, elab_ms, kernel_ms, ...), prints per
namespace the share that is theorems, for the namespaces on which most time
is spent.

Usage: python3 -I interface_share.py SRC_DIR[,MORE_DIRS] DECLS_CSV [TOP_N]
"""

import csv
import os
import re
import sys

NS_RE = re.compile(r"^namespace\s+([A-Za-z0-9_.]+)", re.M)
THEOREM_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*theorem\s+([A-Za-z_][A-Za-z0-9_']*)", re.M)


def theorems(srcs):
    names, namespaces, loose = set(), set(), set()
    for src in srcs.split(","):
      for root, _, files in os.walk(src):
        for f in files:
            if not f.endswith(".sw"):
                continue
            text = open(os.path.join(root, f), encoding="utf-8", errors="replace").read()
            m = NS_RE.search(text)
            if m:
                namespaces.add(m.group(1))
            for t in THEOREM_RE.finditer(text):
                if m:
                    names.add(f"{m.group(1)}.{t.group(1)}")
                else:
                    loose.add(t.group(1))
    return names, namespaces, loose


def namespace_of(decl, namespaces):
    parts = decl.split(".")
    for k in range(len(parts) - 1, 0, -1):
        if ".".join(parts[:k]) in namespaces:
            return ".".join(parts[:k])
    return ""


def is_theorem(decl, names, namespaces, loose):
    parts = decl.split(".")
    if any(".".join(parts[:k]) in names for k in range(len(parts), 0, -1)):
        return True
    return not namespace_of(decl, namespaces) and any(p in loose for p in parts)


def main():
    src, decls_csv = sys.argv[1], sys.argv[2]
    top = int(sys.argv[3]) if len(sys.argv) > 3 else 15
    names, namespaces, loose = theorems(src)
    total = {True: 0.0, False: 0.0}
    count = {True: 0, False: 0}
    per_ns = {}
    largest = (0.0, "")
    for row in csv.DictReader(open(decls_csv, encoding="utf-8")):
        ms = float(row["total_ms"])
        first = row["decl"].split(", ")[0]
        thm = is_theorem(first, names, namespaces, loose)
        total[thm] += ms
        count[thm] += 1
        ns = namespace_of(first, namespaces)
        cell = per_ns.setdefault(ns, [0.0, 0.0])
        cell[0 if thm else 1] += ms
        if thm and ms > largest[0]:
            largest = (ms, row["decl"])
    both = total[True] + total[False]
    print(f"declarations {count[True] + count[False]}, {both / 1000:.1f} s")
    print(f"theorems (proofs and their helpers): {count[True]}, {total[True] / 1000:.1f} s, {100 * total[True] / both:.1f}%")
    print(f"the rest (lower bound on a statements-first pass): {count[False]}, {total[False] / 1000:.1f} s, {100 * total[False] / both:.1f}%")
    print(f"largest single theorem: {largest[0] / 1000:.1f} s  {largest[1]}")
    print(f"namespaces by time (theorems s, rest s, name; '' = library, core or unmatched):")
    for ns, (t, r) in sorted(per_ns.items(), key=lambda kv: -(kv[1][0] + kv[1][1]))[:top]:
        print(f"  {t / 1000:8.1f} {r / 1000:8.1f}  {ns}")


if __name__ == "__main__":
    main()
