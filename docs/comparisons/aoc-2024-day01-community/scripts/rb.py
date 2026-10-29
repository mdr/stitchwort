"""Run a program a few times on an input and report wall-clock seconds.

Usage: python3 -I rb.py CWD INPUT RUNS -- COMMAND ARGS...

Runs COMMAND in CWD with INPUT on stdin, one warm-up and then RUNS timed
runs, and prints every time and the last lines of output. Rough: wall clock,
process start-up included.
"""
import subprocess
import sys
import time

cwd, inp, runs = sys.argv[1], sys.argv[2], int(sys.argv[3])
cmd = sys.argv[sys.argv.index("--") + 1:]
times = []
for i in range(runs + 1):
    with open(inp) as f:
        t = time.monotonic()
        r = subprocess.run(cmd, cwd=cwd, stdin=f, capture_output=True, text=True)
        dt = time.monotonic() - t
    if i:
        times.append(dt)
out = (r.stdout + r.stderr).strip().splitlines()
print(" ".join(f"{t:.3f}" for t in times) + f"s exit={r.returncode} :: " + " | ".join(out[-3:])[:300])
