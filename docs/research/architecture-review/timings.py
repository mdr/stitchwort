#!/usr/bin/env python3
"""Summarise a `cargo build --timings` report: workspace units by duration,
test targets counted, and the sum of unit durations.

  timings.py target/cargo-timings/cargo-timing-*.html
"""
import json, re, sys
from collections import Counter

t = open(sys.argv[1]).read()
d = json.loads(re.search(r"const UNIT_DATA = (\[.*?\n\]);", t, re.S).group(1))
ours = [u for u in d if u["name"].startswith("stitchwort")]
total = sum(u["duration"] for u in d)
wall = max(u["start"] + u["duration"] for u in d)
kinds = Counter(u["target"].strip() or "lib" for u in ours)
print(f"units {len(d)}, workspace units {len(ours)}, sum of durations {total:.0f} s, wall {wall:.0f} s")
print("workspace targets by kind:", dict(kinds))
tests = [u for u in ours if "test" in u["target"]]
print(f"test targets: {len(tests)}, their durations: {sum(u['duration'] for u in tests):.0f} s; "
      f"median {sorted(u['duration'] for u in tests)[len(tests)//2] if tests else 0:.1f} s")
for u in sorted(ours, key=lambda u: -u["duration"])[:15]:
    fe = [s[1]["end"] for s in u.get("sections") or [] if s[0] == "frontend"]
    print(f"  {u['name']:24} {u['target']:30} start {u['start']:6.1f} dur {u['duration']:6.1f}"
          + (f" frontend {fe[0]:.1f}" if fe else "") + f" features {','.join(u['features'])}")
