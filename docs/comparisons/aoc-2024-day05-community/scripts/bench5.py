"""Time the day 5 scratch programs: `run`, `run --js` and native executables.

Usage: python3 -I bench5.py [--mains A,B,...] STITCHWORT PROJ RUNS INPUT...

PROJ is the scratch project (src/Scratch/Hello.sw, ParseOnly.sw, Topo.sw and a
copy of aoc/src/Aoc/Year2024/Day05/Day05.sw). Builds native executables into
PROJ/bin once, then runs every program RUNS times on each INPUT after one
warm-up and prints min and max wall-clock seconds with the last output line.
"""
import os
import subprocess
import sys
import time

args = sys.argv[1:]
mains = ["Scratch.Hello.main", "Scratch.ParseOnly.main", "Aoc.Year2024.Day05.main", "Scratch.Topo.main"]
if args[0] == "--mains":  # --mains A,B,... times only those
    mains, args = args[1].split(","), args[2:]
sw, proj, runs, inputs = args[0], args[1], int(args[2]), args[3:]
os.makedirs(os.path.join(proj, "bin"), exist_ok=True)
for m in mains:
    exe = os.path.join(proj, "bin", m)
    if not os.path.exists(exe):
        subprocess.run([sw, "build", "--native", m, "-o", exe], cwd=proj, check=True, capture_output=True)


def time_one(cmd, inp):
    best, worst, last = 1e9, 0.0, ""
    for i in range(runs + 1):
        with open(inp) as f:
            t = time.monotonic()
            r = subprocess.run(cmd, cwd=proj, stdin=f, capture_output=True, text=True)
            dt = time.monotonic() - t
        last = (r.stdout + r.stderr).strip().splitlines()[-1:] or [""]
        if i:
            best, worst = min(best, dt), max(worst, dt)
    return f"{best:.2f}-{worst:.2f}", last[0][:60]


for inp in inputs:
    print("##", os.path.basename(inp))
    for m in mains:
        for mode, cmd in [("run", [sw, "run", m]), ("js", [sw, "run", "--js", m]),
                          ("native", [os.path.join(proj, "bin", m)])]:
            t, out = time_one(cmd, inp)
            print(f"{m:28} {mode:6} {t:>10}  {out}", flush=True)
