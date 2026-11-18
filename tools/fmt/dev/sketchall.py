#!/usr/bin/env python3
"""Run the twin's `sketch` stage (SW-3955's `hangs` and `settled1`, not in
the repo's twin) over the outputs in folders `probe.py` wrote, and list
those whose lines don't hang. `hangs.py` checks the same predicate in
Python with any twin.

  tools/fmt/dev/sketchall.py --twin TWIN OUT [OUT ...]
"""
import argparse, subprocess
from pathlib import Path
ap = argparse.ArgumentParser()
ap.add_argument("--twin", required=True)
ap.add_argument("out", nargs="+")
args = ap.parse_args()
bad = []; n = 0
for folder in args.out:
    folder = Path(folder).resolve()
    outs = sorted(str(q) for q in folder.glob("*.out.sw"))
    (folder / "list2.txt").write_text("".join(q + "\n" for q in outs))
    out = subprocess.run([*args.twin.split(), "--stage", "sketch", "--batch", str(folder / "list2.txt")], capture_output=True).stdout.decode()
    for block in out.split("\x1e")[1:]:
        path, rest = block.split("\n", 1); n += 1
        if "hangs True" not in rest: bad.append((path, rest.split("\n")[1]))
print(n, "outputs;", len(bad), "not hanging"); [print(b) for b in bad]
