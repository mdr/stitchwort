#!/usr/bin/env python3
"""A crude parallel `check` (SW-1170): one `stitchwort check NS` process per
namespace, at most N at once, each started when the namespaces it uses have
finished, all sharing one check cache. A namespace's process replays what
it uses from the cache, checks the namespace and writes its entry.

  sched.py SW PROJECT_DIR NS_GRAPH CACHE_DIR N [--only NS,...] [--cost COLD_ERR]

--only     run just these namespaces (an edit: the edited one and its
           dependents); the rest must be in the cache already.
--cost     the cold run's STITCHWORT_TIMINGS output, to start the ready
           namespace with the longest remaining path first (else by name).

Prints the wall time, the summed CPU of the jobs, the largest job's peak
RSS and the peak of the summed RSS of the jobs running at once (an upper
bound: each job's peak, held for its whole run), then one line per job.
"""

import os
import subprocess
import sys
import time
from collections import defaultdict


def main():
    args = sys.argv[1:]
    only = None
    cost_file = None
    if "--only" in args:
        i = args.index("--only")
        only = set(args[i + 1].split(","))
        del args[i : i + 2]
    if "--cost" in args:
        i = args.index("--cost")
        cost_file = args[i + 1]
        del args[i : i + 2]
    sw, project, graph_path, cache, n = args
    n = int(n)
    deps = {}
    with open(graph_path) as f:
        for line in f:
            name, _, ds = line.rstrip("\n").partition("\t")
            deps[name] = [d for d in ds.split(",") if d]
    nodes = set(deps) if only is None else only
    cost = defaultdict(float)
    if cost_file:
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        from model import unit_rows

        cost.update(unit_rows(cost_file))
    users = defaultdict(list)
    waiting = {}
    for x in nodes:
        ds = [d for d in deps[x] if d in nodes]
        waiting[x] = len(ds)
        for d in ds:
            users[d].append(x)
    bottom = {}

    def bl(x):
        if x not in bottom:
            bottom[x] = cost[x] + max((bl(u) for u in users[x]), default=0.0)
        return bottom[x]

    ready = sorted((x for x in nodes if waiting[x] == 0), key=lambda x: (-bl(x), x))
    running = {}  # pid -> (name, start, popen)
    log = []
    t0 = time.monotonic()
    failed = []
    rss_now = 0
    rss_peak_sum = 0
    while ready or running:
        while ready and len(running) < n:
            x = ready.pop(0)
            p = subprocess.Popen(
                [sw, "check", "--cache-dir", cache, x],
                cwd=project,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
            )
            running[p.pid] = (x, time.monotonic(), p)
        pid, status, ru = os.wait4(-1, 0)
        if pid not in running:
            continue
        x, start, p = running.pop(pid)
        end = time.monotonic()
        err = p.stderr.read().decode(errors="replace")
        p.stderr.close()
        if os.waitstatus_to_exitcode(status) != 0:
            failed.append((x, err[-500:]))
        rss = ru.ru_maxrss  # bytes on macOS
        log.append((x, start - t0, end - t0, ru.ru_utime + ru.ru_stime, rss))
        for u in users[x]:
            waiting[u] -= 1
            if waiting[u] == 0:
                ready.append(u)
        ready.sort(key=lambda y: (-bl(y), y))
    wall = time.monotonic() - t0
    # Summed peak RSS of the jobs alive at each start.
    events = sorted([(s, r) for _, s, _, _, r in log] + [(e, -r) for _, _, e, _, r in log])
    for _, r in events:
        rss_now += r
        rss_peak_sum = max(rss_peak_sum, rss_now)
    cpu = sum(c for *_, c, _ in log)
    print(f"jobs {len(log)}  N={n}  wall {wall:.2f} s  cpu {cpu:.2f} s  "
          f"max job RSS {max(r for *_, r in log) / 2**20:.0f} MB  "
          f"peak summed RSS {rss_peak_sum / 2**20:.0f} MB  failed {len(failed)}")
    for x, err in failed:
        print(f"FAILED {x}: {err}")
    for x, s, e, c, r in sorted(log, key=lambda l: l[1]):
        print(f"{x}\t{s:.2f}\t{e:.2f}\t{c:.2f}\t{r // 2**20}")


if __name__ == "__main__":
    main()
