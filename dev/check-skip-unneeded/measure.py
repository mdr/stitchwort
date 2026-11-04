#!/usr/bin/env python3
"""SW-1193: a warm `stitchwort check` of aoc after one edit, today against
STITCHWORT_SKIP_UNNEEDED=1 (the prototype). Usage:

    measure.py BASE_BINARY PROTO_BINARY AOC_DIR [RUNS]

For each of four edits (a Tests, a Proofs, a day's code namespace, and
Aoc.Common) it warms the cache, then for each round appends a fresh comment
to the file (so the namespace and its dependents are cache misses, as for a
real edit) and runs the two binaries, one edit each. Prints one line per run
(wall, CPU = user+sys, split of STITCHWORT_TIMINGS rows) and the medians.
The edited file is restored with `git checkout` at the end of each edit.
"""
import os, re, statistics, subprocess, sys, time

EDITS = [
    ("tests", "src/Aoc/Year2025/Day05/Tests/Examples.sw"),
    ("proofs", "src/Aoc/Year2025/Day05/Proofs/Part2.sw"),
    ("code", "src/Aoc/Year2025/Day05/Day05.sw"),
    ("common", "src/Aoc/Common/Range.sw"),
]

def run(binary, aoc, env_extra):
    env = dict(os.environ, STITCHWORT_TIMINGS="1", **env_extra)
    t0 = time.time()
    p = subprocess.Popen([binary, "check"], cwd=aoc, env=env,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    out = p.communicate()[0]
    return time.time() - t0, out

def run_cpu(binary, aoc, env_extra):
    import resource
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    wall, out = run(binary, aoc, env_extra)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (after.ru_utime - before.ru_utime) + (after.ru_stime - before.ru_stime)
    return wall, cpu, out

def split(out):
    """Sum elab+kernel ms of the timings rows: core+std, project namespaces
    replayed ('(cached)'), project namespaces checked."""
    sums = {"core+std": 0.0, "replayed": 0.0, "checked": 0.0}
    n = {"replayed": 0, "checked": 0}
    for line in out.splitlines():
        if line.startswith("total"):
            break
        m = re.match(r"^(\S+)( \(cached\))?\s+([\d.]+)\s+([\d.]+)\s+\d+\s+\d+\s*$", line)
        if not m:
            continue
        label, cached, e, k = m.group(1), m.group(2), float(m.group(3)), float(m.group(4))
        if label == "core" or label.startswith("std/"):
            sums["core+std"] += e + k
        elif cached:
            sums["replayed"] += e + k; n["replayed"] += 1
        else:
            sums["checked"] += e + k; n["checked"] += 1
    return sums, n

def main():
    base, proto, aoc = sys.argv[1:4]
    rounds = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    aoc = os.path.abspath(aoc)
    for label, path in EDITS:
        subprocess.run(["git", "checkout", "--", path], cwd=aoc, check=True)
        run_cpu(base, aoc, {})  # warm (the two binaries have separate cache entries)
        run_cpu(proto, aoc, {})
        res = {"base": [], "proto": []}
        for i in range(rounds):
            for name, binary, env in (("base", base, {}),
                                      ("proto", proto, {"STITCHWORT_SKIP_UNNEEDED": "1"})):
                with open(os.path.join(aoc, path), "a") as f:
                    f.write(f"\n-- touch {name} {i} {time.time()}\n")
                load = os.getloadavg()[0]
                wall, cpu, out = run_cpu(binary, aoc, env)
                sums, n = split(out)
                skip = re.search(r"skip-unneeded: .*", out)
                ok = "checked " in out and "error" not in out.lower()
                res[name].append((wall, cpu))
                print(f"{label:7} {name:5} #{i} wall {wall:6.2f}s cpu {cpu:5.2f}s load {load:5.1f}"
                      f" | core+std {sums['core+std']:7.0f}ms replayed {sums['replayed']:7.0f}ms ({n['replayed']})"
                      f" checked {sums['checked']:7.0f}ms ({n['checked']})"
                      f"{' | ' + skip.group(0) if skip else ''}{'' if ok else ' | FAILED'}", flush=True)
                if not ok:
                    print(out[:600])
        subprocess.run(["git", "checkout", "--", path], cwd=aoc, check=True)
        for name in ("base", "proto"):
            w = statistics.median(x[0] for x in res[name]); c = statistics.median(x[1] for x in res[name])
            print(f"== {label:7} {name:5} median wall {w:.2f}s cpu {c:.2f}s", flush=True)

main()
