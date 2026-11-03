#!/usr/bin/env python3
"""Change coupling from git history (docs/research/architecture-review.md).

  cochange.py [--since DATE] [--max-files N]

Reads `git log --no-merges --name-only` for commits touching crates/, keeps
Rust and .sw sources under crates/*/src (a crate's std library counts as one
unit, `elab/std`), and prints: how many commits touch each crate, how often a
commit spans several crates, the files changed most, and the file pairs that
change together most (with the share of the less-changed file's commits).
Commits touching more than N source files (default 25: sweeps, renames) are
left out of the pair counts.
"""
import argparse, subprocess
from collections import Counter
from itertools import combinations


def unit(path):
    parts = path.split("/")
    if len(parts) < 3 or parts[0] != "crates":
        return None
    crate = parts[1]
    if len(parts) > 3 and parts[2] == "src" and parts[3] == "std":
        return f"{crate}/std"
    if parts[2] != "src" or not (path.endswith(".rs") or path.endswith(".sw")):
        return None
    return f"{crate}/" + "/".join(parts[3:])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--since", default="2026-10-01")
    ap.add_argument("--max-files", type=int, default=25)
    ap.add_argument("--focus", nargs="*", default=[])
    a = ap.parse_args()
    out = subprocess.run(
        ["git", "log", "--no-merges", f"--since={a.since}", "--name-only", "--format=@@%H", "--", "crates"],
        capture_output=True, text=True, check=True,
    ).stdout
    commits = []
    for block in out.split("@@")[1:]:
        lines = block.strip().splitlines()[1:]
        units = {u for u in (unit(l) for l in lines) if u}
        if units:
            commits.append(units)
    files, crates_n, pairs, spans = Counter(), Counter(), Counter(), Counter()
    for units in commits:
        cs = {u.split("/")[0] for u in units}
        for c in cs:
            crates_n[c] += 1
        spans[len(cs)] += 1
        for u in units:
            files[u] += 1
        if len(units) <= a.max_files:
            for p in combinations(sorted(units), 2):
                pairs[p] += 1
    n = len(commits)
    print(f"commits touching crate sources: {n}")
    print("crates per commit: " + ", ".join(f"{k}: {v}" for k, v in sorted(spans.items())))
    print("\ncommits per crate")
    for c, v in crates_n.most_common():
        print(f"  {c:16} {v:5}  {100 * v / n:4.0f}%")
    print("\nfiles changed most")
    for f, v in files.most_common(30):
        print(f"  {f:40} {v:5}")
    print("\npairs changed together most (count, share of the rarer file's commits)")
    for (x, y), v in pairs.most_common(40):
        print(f"  {v:4} {100 * v / min(files[x], files[y]):4.0f}%  {x} + {y}")
    for f in a.focus:
        print(f"\nchanged with {f} ({files[f]} commits)")
        co = Counter()
        for units in commits:
            if f in units and len(units) <= a.max_files:
                for u in units - {f}:
                    co[u] += 1
        for u, v in co.most_common(15):
            print(f"  {v:4} {100 * v / files[f]:4.0f}%  {u}")


if __name__ == "__main__":
    main()
