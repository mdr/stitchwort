#!/usr/bin/env python3
"""Namespace dependency graph of a Stitchwort project, from source text only
(SW-4614, docs/proposals/parallel-checking.md section 3.4).

Reads every .sw file under a project's source folder, takes each file's
`namespace` line, its `import`s and its qualified references, and builds
namespace -> namespaces it uses, following the three rules of
`Elaborator::namespace_edges` (crates/elab/src/project.rs): an import's
path (the longest namespace equal to it), an imported item that is itself
a namespace (`import Aoc.Year2020.Day14 (Spec)`), and a qualified
reference, written from a project root or through an imported qualifier,
to the longest namespace that is a proper prefix of it. It is an
approximation from text, not the parsed tree: comments are stripped
crudely, a local name that shadows a qualifier still counts, and names
brought in by `(..)` are not followed (the import's own edge covers them).
It can only add edges the real graph lacks or miss ones through unusual
spellings; on tools/fmt, AoC and the roguelike it finds no cycle.

Given a per-unit time table (the `fmt-units.csv` of SW-4608: unit,
elab_ms, kernel_ms, ...), it weighs each namespace by elab + kernel ms and
reports total work, the critical path, the parallelism bound (work /
critical path) and greedy list schedules on P workers (each ready
namespace goes to the first free worker, ties by name as in
`canonical_order`). Library files are not in the graph: their time is
reported separately, as a block checked first.

Usage: python3 -I ns_graph.py SRC_DIR [UNITS_CSV]
"""

import csv
import heapq
import os
import re
import sys

NS_RE = re.compile(r"^namespace\s+([A-Za-z0-9_.]+)", re.M)
IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)[ \t]*(?:\(([^)]*)\))?", re.M)
ITEM_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
QUAL_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_%']+)+)")


def strip_comments(text):
    out = []
    for line in text.splitlines():
        i = line.find("--")
        out.append(line if i < 0 else line[:i])
    return "\n".join(out)


def read_project(src):
    """The project's namespaces and their texts: `src` is a source folder or
    a list of them (a project may name several in `stitchwort.yaml`)."""
    dirs = [src] if isinstance(src, (str, bytes, os.PathLike)) else list(src)
    files = {}  # namespace -> list of texts
    for src_dir in dirs:
        for root, _, names in os.walk(src_dir):
            for n in sorted(names):
                if not n.endswith(".sw"):
                    continue
                text = open(os.path.join(root, n), encoding="utf-8").read()
                m = NS_RE.search(text)
                if m:
                    files.setdefault(m.group(1), []).append(strip_comments(text))
    return files


def longest_namespace(path, namespaces, equal):
    parts = path.split(".")
    for k in range(len(parts), 0, -1):
        q = ".".join(parts[:k])
        if q in namespaces and (equal or k < len(parts)):
            return q
    return None


def edges(files):
    namespaces = set(files)
    roots = {n.split(".")[0] for n in namespaces}
    prefixes = set()
    for n in namespaces:
        parts = n.split(".")
        prefixes.update(".".join(parts[:k]) for k in range(1, len(parts) + 1))
    uses = {}
    for ns, texts in files.items():
        found = set()
        for t in texts:
            # Qualifiers this file imports: local name -> the paths it stands for.
            qualifiers = {}
            for path, items in IMPORT_RE.findall(t):
                q = longest_namespace(path, namespaces, True)
                if q:
                    found.add(q)
                for item in ITEM_RE.findall(items or ""):
                    key = "%s.%s" % (path, item)
                    if key in namespaces:
                        found.add(key)
                    if key in prefixes:
                        qualifiers.setdefault(item, []).append(key)
            for ref in QUAL_RE.findall(t):
                first, rest = ref.split(".", 1)
                fulls = [ref] if first in roots else []
                fulls += ["%s.%s" % (key, rest) for key in qualifiers.get(first, [])]
                for full in fulls:
                    q = longest_namespace(full, namespaces, False)
                    if q:
                        found.add(q)
        found.discard(ns)
        uses[ns] = found
    return uses


def graph(src):
    """The graph a project's sources give: `(uses, order, users)`.

    `uses[n]` is the set of project namespaces `n` uses, `order` is a
    topological order (ties by name, as `canonical_order`) and
    `users[t]` lists the namespaces that use `t`. `src` is a source folder
    or a list of them."""
    uses = edges(read_project(src))
    order, users = topo(uses)
    return uses, order, users


def topo(uses):
    waiting = {n: len(u) for n, u in uses.items()}
    users = {n: [] for n in uses}
    for n, u in uses.items():
        for t in u:
            users[t].append(n)
    ready = [n for n, w in waiting.items() if w == 0]
    heapq.heapify(ready)
    order = []
    while ready:
        n = heapq.heappop(ready)
        order.append(n)
        for v in users[n]:
            waiting[v] -= 1
            if waiting[v] == 0:
                heapq.heappush(ready, v)
    if len(order) != len(uses):
        raise SystemExit("cycle among: %s" % sorted(set(uses) - set(order)))
    return order, users


def critical_path(uses, order, w):
    finish, prev = {}, {}
    for n in order:
        start, p = 0.0, None
        for t in uses[n]:
            if finish[t] > start:
                start, p = finish[t], t
        finish[n] = start + w.get(n, 0.0)
        prev[n] = p
    end = max(finish, key=finish.get)
    path = []
    while end:
        path.append(end)
        end = prev[end]
    return finish, list(reversed(path))


def depth_width(uses, order):
    level = {}
    for n in order:
        level[n] = 1 + max((level[t] for t in uses[n]), default=0)
    width = {}
    for n, l in level.items():
        width[l] = width.get(l, 0) + 1
    return max(level.values()), max(width.values())


def schedule(uses, users, w, workers):
    waiting = {n: len(u) for n, u in uses.items()}
    ready = [n for n, k in waiting.items() if k == 0]
    heapq.heapify(ready)
    running = []  # (finish, name)
    free, now, done = workers, 0.0, 0
    while done < len(uses):
        while ready and free:
            n = heapq.heappop(ready)
            heapq.heappush(running, (now + w.get(n, 0.0), n))
            free -= 1
        now, n = heapq.heappop(running)
        free += 1
        done += 1
        for v in users[n]:
            waiting[v] -= 1
            if waiting[v] == 0:
                heapq.heappush(ready, v)
    return now


def main():
    src = sys.argv[1]
    uses, order, users = graph(src)
    depth, width = depth_width(uses, order)
    n_edges = sum(len(u) for u in uses.values())
    print("namespaces %d, edges %d, depth %d, widest level %d" % (len(uses), n_edges, depth, width))
    if len(sys.argv) < 3:
        return
    w, lib = {}, 0.0
    for row in csv.DictReader(open(sys.argv[2])):
        ms = float(row["elab_ms"]) + float(row["kernel_ms"])
        if row["unit"] in uses:
            w[row["unit"]] = ms / 1000
        else:
            lib += ms / 1000
    missing = sorted(set(uses) - set(w))
    if missing:
        print("no time for %d namespaces (counted as 0): %s" % (len(missing), ", ".join(missing)))
    total = sum(w.values())
    finish, path = critical_path(uses, order, w)
    cp = finish[path[-1]]
    print("library and core block: %.1f s" % lib)
    print("project work: %.1f s; critical path %.1f s over %d namespaces; bound %.2fx"
          % (total, cp, len(path), total / cp))
    print("critical path:")
    for n in path:
        print("  %8.1f s  %s" % (w.get(n, 0.0), n))
    top = sorted(w.items(), key=lambda kv: -kv[1])[:8]
    print("largest namespaces: " + ", ".join("%s %.1f s" % kv for kv in top))
    for p in (1, 2, 4, 6, 8, 10):
        t = schedule(uses, users, w, p)
        print("P=%2d: project %.1f s (%.2fx); with the library block first %.1f s (%.2fx)"
              % (p, t, total / t, t + lib, (total + lib) / (t + lib)))


if __name__ == "__main__":
    main()
