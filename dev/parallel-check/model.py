#!/usr/bin/env python3
"""How much a process-per-namespace parallel `check` could gain (SW-1170).

Reads measurements and prints the model's numbers for
dev/measurements/parallel-checking.md:

  model.py COLD_ERR WARM_ERR NS_GRAPH STD_GRAPH WARM_EACH [EDIT_NS...]

COLD_ERR   stderr of `STITCHWORT_TIMINGS=1 stitchwort check --no-cache`
WARM_ERR   the same with every entry a cache hit (per-unit replay times)
NS_GRAPH   `ns_graph PROJECT` output (namespace, direct deps)
STD_GRAPH  `ns_graph --std` output (library file, files it needs)
WARM_EACH  `warm-each` output (per namespace: CPU of a warm `check NS`,
           RSS, the library files its closure loads)

Work is the unit's elaboration plus kernel time from the cold run (one
process, sequential). A job's overhead in the process design is what a
warm `check NS` costs in CPU (process start, core, parsing the project,
replaying the closure from the cache), less NS's own replay. Schedules are
greedy list schedules, the ready job with the longest remaining path first.
"""

import heapq
import sys
from collections import defaultdict


def unit_rows(path):
    rows = {}
    with open(path) as f:
        lines = f.read().splitlines()
    inside = False
    for line in lines:
        if line.startswith("unit "):
            inside = True
            continue
        if inside and line.startswith("---"):
            break
        if inside:
            parts = line.split()
            label = parts[0]
            elab, kernel = float(parts[-4]), float(parts[-3])
            rows[label] = (elab + kernel) / 1000.0
    return rows


def outside(path):
    """The run's time outside the units (parsing, core load, printing)."""
    with open(path) as f:
        for line in f:
            if line.startswith("wall ") and "outside the units" in line:
                return float(line.split(")")[-1].split()[0]) / 1000.0
    return 0.0


def graph(path):
    g = {}
    with open(path) as f:
        for line in f:
            name, _, deps = line.rstrip("\n").partition("\t")
            g[name] = [d for d in deps.split(",") if d]
    return g


def warm_each(path):
    out = {}
    with open(path) as f:
        for line in f:
            ns, user, sys_, rss, std = (line.rstrip("\n").split("\t") + [""])[:5]
            out[ns] = (float(user) + float(sys_), int(rss), [s for s in std.split(",") if s])
    return out


def longest_paths(nodes, deps, cost):
    """Longest path ending at each node (inclusive) and the path to it."""
    memo = {}

    def go(n):
        if n in memo:
            return memo[n]
        best, via = 0.0, None
        for d in deps.get(n, []):
            if d in nodes:
                v = go(d)[0]
                if v > best:
                    best, via = v, d
        memo[n] = (best + cost[n], via)
        return memo[n]

    sys.setrecursionlimit(10000)
    for n in nodes:
        go(n)
    return memo


def critical(nodes, deps, cost):
    memo = longest_paths(nodes, deps, cost)
    end = max(nodes, key=lambda n: memo[n][0])
    path, n = [], end
    while n is not None:
        path.append(n)
        n = memo[n][1]
    return memo[end][0], list(reversed(path))


def schedule(nodes, deps, cost, workers):
    """Makespan of a greedy list schedule on `workers` identical workers."""
    users = defaultdict(list)
    waiting = {}
    for n in nodes:
        ds = [d for d in deps.get(n, []) if d in nodes]
        waiting[n] = len(ds)
        for d in ds:
            users[d].append(n)
    # Priority: longest path from the node to the end (bottom level).
    bottom = {}

    def bl(n):
        if n not in bottom:
            bottom[n] = cost[n] + max((bl(u) for u in users[n]), default=0.0)
        return bottom[n]

    for n in nodes:
        bl(n)
    ready = [(-bottom[n], n) for n in nodes if waiting[n] == 0]
    heapq.heapify(ready)
    running = []  # (finish, node)
    t = 0.0
    free = workers
    done = 0
    while done < len(nodes):
        while free and ready:
            _, n = heapq.heappop(ready)
            heapq.heappush(running, (t + cost[n], n))
            free -= 1
        t, n = heapq.heappop(running)
        free += 1
        done += 1
        for u in users[n]:
            waiting[u] -= 1
            if waiting[u] == 0:
                heapq.heappush(ready, (-bottom[u], u))
    return t


def main():
    cold_err, warm_err, ns_graph, std_graph, each_path = sys.argv[1:6]
    edits = sys.argv[6:]
    cold = unit_rows(cold_err)
    warm = {k.replace(" (cached)", ""): v for k, v in unit_rows(warm_err).items()}
    # A cached row's label is "name (cached)": unit_rows keeps the first word.
    nsg = graph(ns_graph)
    stdg = graph(std_graph)
    each = warm_each(each_path)

    project = set(nsg)
    std = {u for u in cold if u.startswith("std/")}
    nodes = project | std
    deps = {}
    for n in project:
        deps[n] = list(nsg[n]) + [s for s in each[n][2] if s in std]
    for s in std:
        deps[s] = [d for d in stdg.get(s, []) if d in std]
    work = {n: cold[n] for n in nodes}
    core = cold["core"] + outside(cold_err)

    total = sum(work.values()) + core
    print(f"units: {len(project)} namespaces, {len(std)} library files")
    print(f"total work (cold, sequential): {total:.1f} s "
          f"(library {sum(work[s] for s in std):.1f} s, core and parsing {core:.2f} s)")
    cp, path = critical(nodes, deps, work)
    print(f"critical path (no overheads): {cp + core:.1f} s; ideal speedup "
          f"bound {total / (cp + core):.2f}x")
    print("  path: " + " -> ".join(f"{n} ({work[n]:.1f})" for n in path))
    print("\nideal list schedule (no overheads), cold full check:")
    for w in (1, 2, 4, 8, 10):
        m = schedule(nodes, deps, work, w) + core
        print(f"  N={w:2d}: {m:6.1f} s  speedup {total / m:.2f}x")

    # The process design: each job pays its overhead.
    base = min(v[0] for v in each.values())
    over = {}
    for n in project:
        over[n] = max(each[n][0] - warm.get(n, 0.0), 0.0)

    def closure(n):
        clos, todo = set(), list(deps[n])
        while todo:
            d = todo.pop()
            if d not in clos:
                clos.add(d)
                todo.extend(deps[d])
        return clos

    # A library-file job: the cheapest process plus replaying its deps.
    for s in std:
        over[s] = base + sum(warm.get(d, 0.0) for d in closure(s))
    jobs = {n: work[n] + over[n] for n in nodes}
    print(f"\nprocess per unit: overhead per job min {base:.2f} s, "
          f"median (namespaces) {sorted(over[n] for n in project)[len(project) // 2]:.2f} s, "
          f"total {sum(over.values()):.1f} s CPU")

    def report(label, nodes_, deps_, jobs_):
        cp_, path_ = critical(nodes_, deps_, jobs_)
        print(f"\n{label}: {len(nodes_)} jobs, {sum(jobs_[n] for n in nodes_):.1f} s CPU, "
              f"critical path {cp_:.1f} s")
        print("  path: " + " -> ".join(f"{n} ({jobs_[n]:.2f})" for n in path_ if jobs_[n] >= 0.05))
        for w in (1, 2, 4, 8, 10):
            m = schedule(nodes_, deps_, jobs_, w)
            print(f"  N={w:2d}: {m:6.1f} s  speedup {total / m:.2f}x vs sequential {total:.1f} s")

    report("A. a process per namespace and per library file", nodes, deps, jobs)

    # B. The library checked first, in one process (as today), then a
    # process per namespace.
    nodes_b = project | {"<library>"}
    deps_b = {n: [d for d in nsg[n]] + ["<library>"] for n in project}
    deps_b["<library>"] = []
    jobs_b = {n: jobs[n] for n in project}
    jobs_b["<library>"] = sum(work[s] for s in std) + core
    report("B. the library in one process first, then a process per namespace",
           nodes_b, deps_b, jobs_b)

    # C. A process per group: a namespace with its .Spec, .Proofs and .Tests
    # (Aoc.Year2021.Day16 and the three under it), checked in one process.
    def group(n):
        parts = n.split(".")
        while len(parts) > 1 and parts[-1] in ("Proofs", "Tests", "Spec"):
            parts.pop()
        return ".".join(parts)

    groups = defaultdict(list)
    for n in project:
        groups[group(n)].append(n)
    gnodes = set(groups) | std
    gdeps = {s: deps[s] for s in std}
    gjobs = {s: jobs[s] for s in std}
    for g, members in groups.items():
        ext = set()
        for m in members:
            ext |= {group(d) if d in project else d for d in deps[m]}
        ext.discard(g)
        gdeps[g] = sorted(ext)
        gjobs[g] = sum(work[m] for m in members) + max(over[m] for m in members)
    report("C. a process per group (a namespace with its Spec, Proofs, Tests), "
           "library files as in A", gnodes, gdeps, gjobs)

    # D. Long-lived workers (a pool of N processes, or threads), each job
    # paying only the replay of its closure (its overhead less the fixed
    # cost of a process: start, core, parsing). An upper bound on what a
    # pool pays, since a worker keeps what it loaded for earlier jobs.
    jobs_d = {n: work[n] + max(over[n] - base, 0.0) for n in nodes}
    report("D. a pool of long-lived workers: each job replays its closure, "
           "no process start, core or parsing", nodes, deps, jobs_d)

    rss = sorted(v[1] for v in each.values())
    print(f"\nworker RSS after replaying its closure (warm check NS): "
          f"median {rss[len(rss) // 2] / 2**20:.0f} MB, max {rss[-1] / 2**20:.0f} MB")

    # Edits: an edited namespace and everything that uses it are re-checked.
    users = defaultdict(set)
    for n in project:
        for d in nsg[n]:
            users[d].add(n)

    def dependents(n):
        seen, todo = set(), [n]
        while todo:
            x = todo.pop()
            if x not in seen:
                seen.add(x)
                todo.extend(users[x])
        return seen

    replay_all = sum(warm.get(n, 0.0) for n in nodes) + warm["core"] + outside(warm_err)
    print(f"\nwarm full check (everything a hit): {replay_all:.1f} s (summed replay, core, parsing)")
    print("\nedits: the namespace and its dependents re-checked, the rest hits.")
    print("  today = `check` of the whole project (replays every other namespace);")
    print("  one = one process checking only the affected namespaces (replays their closure);")
    print("  par10 = a process per affected namespace, 10 at once.")
    print("  edited                         affected  today s  one s  par10 s  par10/one")
    rows = []
    for n in sorted(project):
        aff = dependents(n)
        w_aff = sum(work[a] for a in aff)
        today = replay_all - sum(warm.get(a, 0.0) for a in aff) + w_aff
        one = max(over[a] for a in aff) + w_aff
        par = schedule(aff, deps, jobs, 10)
        rows.append((n, len(aff), today, one, par))
    for n, k, today, one, par in rows:
        if n in edits:
            print(f"  {n:30s} {k:8d} {today:8.1f} {one:6.1f} {par:8.1f}  {one / par:.2f}x")
    kinds = defaultdict(list)
    for r in rows:
        last = r[0].split(".")[-1]
        kind = last if last in ("Proofs", "Tests", "Spec") else "code"
        kinds[kind].append(r)
    print("\n  by kind of namespace edited (means):")
    for kind, rs in sorted(kinds.items()):
        mean = lambda i: sum(r[i] for r in rs) / len(rs)
        sp = sum(r[3] / r[4] for r in rs) / len(rs)
        print(f"  {kind:8s} n={len(rs):3d} affected {mean(1):5.1f}  today {mean(2):5.2f} s  "
              f"one {mean(3):5.2f} s  par10 {mean(4):5.2f} s  par10 speedup over one {sp:.2f}x")


if __name__ == "__main__":
    main()
