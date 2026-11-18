#!/usr/bin/env python3
"""Sort the twin's outputs in a folder `probe.py` wrote by how they differ
from Rust's `stitchwort fmt -` on the same input: `glue:` pairs of tokens
the twin spaces and Rust glues (the pair kinds: n a digit, a a letter),
`layout` for the same tokens on other lines, `other` for the rest.

  tools/fmt/dev/classify.py OUT [--bin STITCHWORT]
"""
import argparse, subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
ap = argparse.ArgumentParser()
ap.add_argument("out")
ap.add_argument("--bin", default=str(ROOT / "target/release/stitchwort"))
args = ap.parse_args()
BIN = args.bin
folder = Path(args.out)
kinds = {}
for q in sorted(folder.glob("*.out.sw")):
    p = Path(str(q)[:-7] + ".sw")
    out = q.read_text()
    rust = subprocess.run([BIN, "fmt", "-"], input=p.read_bytes(), capture_output=True).stdout.decode()
    if rust == out: continue
    a, b = out.split("\n"), rust.split("\n")
    if len(a) == len(b) and all(x.replace(" ", "") == y.replace(" ", "") for x, y in zip(a, b)):
        pairs = set()
        for x, y in zip(a, b):
            if x != y:
                # find glued pairs in rust's line where twin has a space
                i = j = 0
                while i < len(x) and j < len(y):
                    if x[i] == y[j]: i += 1; j += 1
                    elif x[i] == " ": pairs.add((y[j-1], y[j])); i += 1
                    else: pairs.add(("?", "?")); break
        def cls(c): return "n" if c.isdigit() else "a" if c.isalpha() else c
        k = "glue:" + ",".join(sorted({cls(l) + cls(r) for l, r in pairs}))
    elif out.replace(" ", "").replace("\n", "") == rust.replace(" ", "").replace("\n", ""):
        k = "layout"
    else:
        k = "other"
    kinds.setdefault(k, []).append(p.name)
for k, v in sorted(kinds.items(), key=lambda kv: -len(kv[1])):
    print(len(v), k, v[:5])
