"""Run a Stitchwort program once on an input and report wall-clock seconds.

Usage: python3 -I rb.py CWD INPUT -- COMMAND ARGS...

Runs COMMAND in CWD with INPUT on stdin, one run, and prints the wall time
and the last lines of output. Rough: one run, no warm-up.
"""
import subprocess
import sys
import time

cwd, inp = sys.argv[1], sys.argv[2]
cmd = sys.argv[sys.argv.index("--") + 1:]
with open(inp) as f:
    t = time.monotonic()
    r = subprocess.run(cmd, cwd=cwd, stdin=f, capture_output=True, text=True)
    dt = time.monotonic() - t
out = (r.stdout + r.stderr).strip().splitlines()
print(f"{dt:.2f}s exit={r.returncode} :: " + " | ".join(out[-4:])[:400])
