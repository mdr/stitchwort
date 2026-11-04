#!/usr/bin/env python3
"""CPU (user+sys) and wall per command against a warm cache, medians of N.

measure.py BIN PROJECT_DIR N [--env K=V]... [--only NAME,...]
Prints one line per run and a median table. STITCHWORT_STD_DIR must be set
if BIN is outside a checkout.
"""
import os, resource, statistics, subprocess, sys, time

def commands(proj):
    inp = os.path.join(proj, "inputs/2025/day04.txt")
    return [
        ("floor", ["check", os.path.join(proj, "..", "one.sw")], None),
        ("check", ["check"], None),
        ("check-index", ["check", "--index", os.devnull], None),
        ("test", ["test"], None),
        ("run", ["run", "Aoc.Year2025.Day04.main"], inp),
        ("audit", ["audit", "--no-search"], None),
        ("search", ["search", "List.length"], None),
    ]

def once(binary, args, stdin, env, cwd):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    t = time.monotonic()
    with open(stdin or os.devnull) as f:
        p = subprocess.run([binary] + args, cwd=cwd, env=env, stdin=f,
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    wall = time.monotonic() - t
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
    return cpu, wall, p.returncode, p.stderr.decode()

def main():
    binary, proj, n = sys.argv[1], os.path.abspath(sys.argv[2]), int(sys.argv[3])
    env = dict(os.environ)
    only = None
    rest = sys.argv[4:]
    while rest:
        if rest[0] == "--env":
            k, v = rest[1].split("=", 1); env[k] = v; rest = rest[2:]
        elif rest[0] == "--only":
            only = rest[1].split(","); rest = rest[2:]
        else:
            sys.exit(f"unknown {rest[0]}")
    one = os.path.join(proj, "..", "one.sw")
    if not os.path.exists(one):
        open(one, "w").write("def one: Nat := 1\n")
    cmds = [c for c in commands(proj) if only is None or c[0] in only]
    res = {c[0]: [] for c in cmds}
    for r in range(n):
        for name, args, stdin in cmds:
            cpu, wall, rc, err = once(binary, args, stdin, env, proj)
            res[name].append((cpu, wall))
            print(f"round {r} {name:12} cpu {cpu:6.2f} wall {wall:6.2f} rc {rc} load {os.getloadavg()[0]:.0f}", flush=True)
            if env.get("SHOW_STDERR"):
                sys.stderr.write(err)
    print("\n| command | CPU median | wall median |\n|---|---:|---:|")
    for name, rs in res.items():
        print(f"| {name} | {statistics.median(c for c, _ in rs):.2f} s | {statistics.median(w for _, w in rs):.2f} s |")

main()
