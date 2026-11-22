#!/usr/bin/env python3
"""A Stitchwort project's namespaces checked as parallel processes (SW-4644,
docs/proposals/parallel-checking.md: the first measurement of option C).

Usage:
    python3 par_check.py PROJECT WORKERS CACHE_DIR STITCHWORT [--compare] [--limit N]

`CACHE_DIR` must be fresh (absent or empty); with `--compare` the sequential
run gets a fresh sibling, `CACHE_DIR-seq`.

What it does:

1. Fills the cache with the standard library, in one process:
   `stitchwort check --std --cache-dir CACHE Std`. `Std` is the one library
   target that `library_files_named` expands to every file
   (crates/elab/src/library.rs:1304: the prefix is empty), and
   `check_library_targets` then loads every file and what it needs in
   canonical order, writing an entry for each. That is the standard library
   only: core is always loaded, not cached. The alternative, checking a
   project namespace that imports nothing, would fill only the library files
   that one namespace happens to use; `--std Std` fills all of them, so the
   per-namespace processes below replay the library instead of elaborating
   it.

2. Schedules every project namespace (or the first `--limit N` in dependency
   order) as its own process,
       stitchwort check --project PROJECT --cache-dir CACHE --timings=1 NS
   each started only once all the namespaces `ns_graph.py` says it uses have
   finished successfully, at most WORKERS at a time; ties by name. A
   namespace whose dependency failed is not started, and is reported as
   blocked.

3. Records each namespace's start, end, exit status, peak resident set size
   (from `/usr/bin/time -l` on macOS) and its own elaboration-plus-kernel
   time (from `--timings`).

4. Prints the schedule's wall time, the sum of the process times, and the
   overhead: the process time minus the namespace's own time, which is what
   the process spent starting up, loading core, and replaying its
   dependencies from the cache.

5. With `--compare`, also runs one sequential check over the same selected
   namespaces into a second cache, compares the sorted warning and error
   lines of the two runs, and compares the two `check/` folders byte for
   byte. The two caches share the standard library entries (copied from the
   first after step 1), so that difference is the project namespaces' work;
   they also share `check/header`, whose random salt is part of every entry.

The graph is from source text, as `ns_graph.py` builds it: an approximation
(the script's header says how). A dependency it misses only means that
process may elaborate a namespace itself instead of replaying its entry; it
does not change a verdict.
"""

import argparse
import difflib
import heapq
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ns_graph  # noqa: E402  (the graph builder this experiment shares)


UNIT_HEADER = re.compile(
    r"^unit\s+elab ms\s+kernel ms\s+nodes\s+decls\s*$", re.M
)
TIME_REPORT = re.compile(
    r"^\s*\d+\.\d+ real\s+\d+\.\d+ user\s+\d+\.\d+ sys\s*$", re.M
)
PEAK_MAC = re.compile(r"^\s*(\d+)\s+maximum resident set size\s*$", re.M)
PEAK_LINUX = re.compile(
    r"^\s*Maximum resident set size \(kbytes\):\s*(\d+)", re.M
)
IS_DARWIN = sys.platform == "darwin"
TIME_COMMAND = "/usr/bin/time"


# --- arguments and project files -------------------------------------------


def arguments():
    parser = argparse.ArgumentParser(
        description="check a Stitchwort project's namespaces as parallel processes"
    )
    parser.add_argument("project", help="the project folder (with stitchwort.yaml)")
    parser.add_argument("workers", type=int, help="how many processes at once (P)")
    parser.add_argument("cache_dir", help="a fresh cache directory")
    parser.add_argument("stitchwort", help="the stitchwort binary")
    parser.add_argument(
        "--compare",
        action="store_true",
        help="also run the sequential check and compare diagnostics and cache entries",
    )
    parser.add_argument(
        "--limit",
        type=int,
        metavar="N",
        help="only the first N namespaces in dependency order",
    )
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("workers must be at least 1")
    if args.limit is not None and args.limit < 1:
        parser.error("--limit must be at least 1")
    args.project = os.path.abspath(args.project)
    args.cache_dir = os.path.abspath(args.cache_dir)
    args.stitchwort = os.path.abspath(args.stitchwort)
    if not os.path.isdir(args.project):
        parser.error("no project folder %s" % args.project)
    if not os.access(args.stitchwort, os.X_OK):
        parser.error("%s is not an executable" % args.stitchwort)
    return args


def source_dirs(project):
    """The folders `sources:` names in stitchwort.yaml, else `src`."""
    config = os.path.join(project, "stitchwort.yaml")
    sources = []
    try:
        lines = open(config, encoding="utf-8").read().splitlines()
    except OSError:
        lines = []
    for i, line in enumerate(lines):
        match = re.match(r"^\s*sources\s*:\s*(.*?)\s*$", line)
        if not match:
            continue
        value = match.group(1).split("#", 1)[0].strip()
        if value.startswith("[") and value.endswith("]"):
            sources = [
                part.strip().strip("\"'")
                for part in value[1:-1].split(",")
                if part.strip()
            ]
        elif value:
            sources = [value.strip("\"'")]
        else:
            for rest in lines[i + 1 :]:
                item = re.match(r"^\s*-\s*(\S.*?)\s*$", rest)
                if not item:
                    break
                sources.append(item.group(1).strip("\"'"))
        break
    if not sources:
        sources = ["src"]
    return [os.path.join(project, source) for source in sources]


def fresh_directory(path):
    """Makes `path` if needed; refuses one that already holds anything."""
    if os.path.exists(path):
        if not os.path.isdir(path):
            sys.exit("error: %s is not a directory" % path)
        if os.listdir(path):
            sys.exit(
                "error: %s is not fresh: it already has files (give an empty "
                "or absent directory)" % path
            )
    else:
        os.makedirs(path)


# --- running one process ----------------------------------------------------


def wrapped(command):
    if IS_DARWIN and os.path.exists(TIME_COMMAND):
        return [TIME_COMMAND, "-l"] + command
    return command


def peak_memory(text):
    match = PEAK_MAC.search(text) or PEAK_LINUX.search(text)
    if not match:
        return None
    value = int(match.group(1))
    if match.re is PEAK_LINUX:
        value *= 1024
    return value


def without_time_report(text):
    match = TIME_REPORT.search(text)
    return text[: match.start()] if match else text


def without_timings(text):
    match = UNIT_HEADER.search(text)
    return text[: match.start()] if match else text


def namespace_time(text, namespace):
    """The namespace's own elab + kernel seconds, from its `--timings` row."""
    start = UNIT_HEADER.search(text)
    if not start:
        return None
    for line in text[start.end() :].splitlines():
        if not line.strip():
            continue
        if line.startswith("-"):
            break
        fields = line.split()
        if len(fields) < 5:
            break
        label = " ".join(fields[:-4])
        if label == namespace or label == namespace + " (cached)":
            try:
                return (float(fields[-4]) + float(fields[-3])) / 1000.0
            except ValueError:
                return None
    return None


NOISE = ("checked ", "note: ")


def diagnostic_lines(text):
    """The warning and error lines of one process's output, timings removed."""
    text = without_timings(without_time_report(text))
    lines = []
    for line in text.splitlines():
        line = line.rstrip()
        if not line.strip():
            continue
        if line.startswith(NOISE):
            continue
        lines.append(line)
    return lines


def run_one(command, project):
    """Runs one process, returns its status, wall time, output and peak."""
    with tempfile.TemporaryFile() as log:
        start = time.monotonic()
        process = subprocess.Popen(
            wrapped(command),
            cwd=project,
            stdout=log,
            stderr=subprocess.STDOUT,
        )
        code = process.wait()
        elapsed = time.monotonic() - start
        log.seek(0)
        text = log.read().decode("utf-8", "replace")
    return {
        "code": code,
        "elapsed": elapsed,
        "text": text,
        "peak": peak_memory(text),
    }


# --- the scheduler ----------------------------------------------------------


def run_parallel(selected, deps, workers, command_for, project):
    waiting = {name: len(deps[name]) for name in selected}
    users = {name: [] for name in selected}
    for name in selected:
        for target in deps[name]:
            users[target].append(name)
    ready = [name for name in selected if waiting[name] == 0]
    heapq.heapify(ready)

    records = {}
    running = {}
    start = time.monotonic()
    while True:
        while ready and len(running) < workers:
            name = heapq.heappop(ready)
            log = tempfile.TemporaryFile()
            launched = time.monotonic() - start
            process = subprocess.Popen(
                wrapped(command_for(name)),
                cwd=project,
                stdout=log,
                stderr=subprocess.STDOUT,
            )
            running[name] = {
                "process": process,
                "log": log,
                "start": launched,
            }
        if not running:
            break
        finished = []
        while not finished:
            finished = [
                name
                for name, run in running.items()
                if run["process"].poll() is not None
            ]
            if not finished:
                time.sleep(0.02)
        for name in sorted(finished):
            run = running.pop(name)
            code = run["process"].returncode
            end = time.monotonic() - start
            run["log"].seek(0)
            text = run["log"].read().decode("utf-8", "replace")
            run["log"].close()
            clean = without_time_report(text)
            records[name] = {
                "start": run["start"],
                "end": end,
                "wall": end - run["start"],
                "code": code,
                "peak": peak_memory(text),
                "own": namespace_time(clean, name),
                "diagnostics": diagnostic_lines(clean),
                "text": clean,
            }
            if code == 0:
                for user in users[name]:
                    waiting[user] -= 1
                    if waiting[user] == 0:
                        heapq.heappush(ready, user)
    blocked = sorted(set(selected) - set(records))
    return time.monotonic() - start, records, blocked


# --- output -----------------------------------------------------------------


def show_seconds(value):
    return "     -  " if value is None else "%8.2f" % value


def show_megabytes(value):
    return "     -" if value is None else "%6.1f" % (value / (1024.0 * 1024.0))


def report(records, wall, blocked, workers):
    width = max([len(name) for name in records] + [9])
    print()
    print("per namespace (times from the schedule's start):")
    print(
        "%-*s  %8s  %8s  %8s  %8s  %8s  %4s  %8s"
        % (width, "namespace", "start", "end", "wall", "own", "overhead", "exit", "peak MB")
    )
    for name in sorted(records, key=lambda n: (records[n]["start"], n)):
        record = records[name]
        overhead = (
            None
            if record["own"] is None
            else max(0.0, record["wall"] - record["own"])
        )
        print(
            "%-*s  %8.2f  %8.2f  %8.2f  %s  %s  %4d  %8s"
            % (
                width,
                name,
                record["start"],
                record["end"],
                record["wall"],
                show_seconds(record["own"]),
                show_seconds(overhead),
                record["code"],
                show_megabytes(record["peak"]),
            )
        )

    process_total = sum(record["wall"] for record in records.values())
    own_total = sum(
        record["own"] for record in records.values() if record["own"] is not None
    )
    measured = [record for record in records.values() if record["own"] is not None]
    overhead_total = (
        sum(max(0.0, record["wall"] - record["own"]) for record in measured)
        if measured
        else None
    )
    peaks = [record["peak"] for record in records.values() if record["peak"] is not None]
    print()
    print("workers: %d" % workers)
    print("total wall time: %.2f s" % wall)
    print("sum of process times: %.2f s" % process_total)
    print("sum of namespaces' own times (--timings): %.2f s" % own_total)
    if overhead_total is None:
        print("overhead (process time - own time): unknown (no --timings rows read)")
    else:
        print(
            "overhead (process time - own time, %d of %d measured): %.2f s"
            % (len(measured), len(records), overhead_total)
        )
    if peaks:
        print("largest peak resident set size: %.1f MB" % (max(peaks) / (1024.0 * 1024.0)))
    if blocked:
        print()
        print("blocked (a namespace they depend on failed): %s" % ", ".join(blocked))


def report_failures(records, blocked):
    failed = [name for name, record in records.items() if record["code"] != 0]
    if not failed and not blocked:
        return 0
    print()
    for name in sorted(failed):
        record = records[name]
        print("FAILED %s (exit %d):" % (name, record["code"]))
        print(record["text"].rstrip())
        print()
    if blocked:
        print("NOT STARTED (a dependency failed): %s" % ", ".join(blocked))
    return 1


# --- the comparison ---------------------------------------------------------


def compare_diagnostics(parallel_lines, sequential_lines):
    left = sorted(sequential_lines)
    right = sorted(parallel_lines)
    print()
    if left == right:
        print(
            "diagnostics: the same %d warning/error line(s), sorted"
            % len(left)
        )
        return True
    print(
        "diagnostics: DIFFERENT (sequential %d line(s), parallel %d)"
        % (len(left), len(right))
    )
    for line in difflib.unified_diff(
        left, right, fromfile="sequential", tofile="parallel", lineterm=""
    ):
        print(line)
    return False


def cache_names(cache_dir):
    folder = os.path.join(cache_dir, "check")
    if not os.path.isdir(folder):
        return []
    return [
        name
        for name in sorted(os.listdir(folder))
        if not name.startswith(".tmp-")
        and os.path.isfile(os.path.join(folder, name))
    ]


def different_bytes(folder_a, folder_b, name):
    """Whether the two files differ; the offset of the first difference."""
    path_a = os.path.join(folder_a, "check", name)
    path_b = os.path.join(folder_b, "check", name)
    if os.path.getsize(path_a) != os.path.getsize(path_b):
        return True, None
    offset = 0
    with open(path_a, "rb") as a, open(path_b, "rb") as b:
        while True:
            chunk_a = a.read(1 << 20)
            chunk_b = b.read(1 << 20)
            if chunk_a != chunk_b:
                for i, (x, y) in enumerate(zip(chunk_a, chunk_b)):
                    if x != y:
                        return True, offset + i
                return True, offset + min(len(chunk_a), len(chunk_b))
            if not chunk_a:
                return False, None
            offset += len(chunk_a)


def compare_caches(parallel_cache, sequential_cache):
    parallel = cache_names(parallel_cache)
    sequential = cache_names(sequential_cache)
    folder_a = parallel_cache
    folder_b = sequential_cache
    only_parallel = sorted(set(parallel) - set(sequential))
    only_sequential = sorted(set(sequential) - set(parallel))
    differing = []
    for name in sorted(set(parallel) & set(sequential)):
        differs, offset = different_bytes(folder_b, folder_a, name)
        if differs:
            differing.append((name, offset))
    print()
    print(
        "cache: %d file(s) from the parallel run, %d from the sequential run"
        % (len(parallel), len(sequential))
    )
    if not only_parallel and not only_sequential and not differing:
        print("cache: every file name matches and every file is byte for byte the same")
        return True
    print("cache: DIFFERENT")
    for name in only_parallel[:20]:
        print("  only in the parallel cache: %s" % name)
    if len(only_parallel) > 20:
        print("  ... and %d more only in the parallel cache" % (len(only_parallel) - 20))
    for name in only_sequential[:20]:
        print("  only in the sequential cache: %s" % name)
    if len(only_sequential) > 20:
        print(
            "  ... and %d more only in the sequential cache"
            % (len(only_sequential) - 20)
        )
    for name, offset in differing[:20]:
        where = "first differing byte at %d" % offset if offset is not None else "different size"
        print("  contents differ: %s (%s)" % (name, where))
    if len(differing) > 20:
        print("  ... and %d more with different contents" % (len(differing) - 20))
    return False


def copy_check_cache(source, destination):
    """Seeds `destination`'s check/ folder with `source`'s entries (the library)."""
    folder = os.path.join(destination, "check")
    os.makedirs(folder, exist_ok=True)
    for name in cache_names(source):
        shutil.copy2(
            os.path.join(source, "check", name), os.path.join(folder, name)
        )


# --- main -------------------------------------------------------------------


def main():
    args = arguments()
    fresh_directory(args.cache_dir)

    dirs = source_dirs(args.project)
    uses, order, users = ns_graph.graph(dirs)
    selected = order[: args.limit] if args.limit is not None else list(order)
    selected_set = set(selected)
    deps = {name: set(uses[name]) & selected_set for name in selected}
    edges = sum(len(targets) for targets in uses.values())
    print(
        "graph: %d namespaces, %d edge(s); checking %d%s"
        % (
            len(order),
            edges,
            len(selected),
            " (--limit %d)" % args.limit if args.limit is not None else "",
        )
    )
    if not selected:
        print("nothing to check")
        return 0

    fill = run_one(
        [
            args.stitchwort,
            "--color",
            "never",
            "check",
            "--std",
            "--cache-dir",
            args.cache_dir,
            "Std",
        ],
        args.project,
    )
    print(
        "standard library fill (`check --std Std`): %.2f s, exit %d%s"
        % (
            fill["elapsed"],
            fill["code"],
            ""
            if fill["peak"] is None
            else ", peak %.1f MB" % (fill["peak"] / (1024.0 * 1024.0)),
        )
    )
    if fill["code"] != 0:
        print(fill["text"].rstrip())
        return fill["code"] if fill["code"] > 0 else 1

    sequential_cache = None
    if args.compare:
        sequential_cache = args.cache_dir + "-seq"
        fresh_directory(sequential_cache)
        # Both runs get the same library entries and the same header salt, so
        # the comparison is of the project namespaces' work.
        copy_check_cache(args.cache_dir, sequential_cache)

    def command_for(name):
        return [
            args.stitchwort,
            "--color",
            "never",
            "check",
            "--project",
            args.project,
            "--cache-dir",
            args.cache_dir,
            "--timings=1",
            name,
        ]

    wall, records, blocked = run_parallel(
        selected, deps, args.workers, command_for, args.project
    )
    report(records, wall, blocked, args.workers)

    status = report_failures(records, blocked)

    if args.compare:
        sequential_command = [
            args.stitchwort,
            "--color",
            "never",
            "check",
            "--project",
            args.project,
            "--cache-dir",
            sequential_cache,
        ]
        if args.limit is not None:
            sequential_command += selected
        sequential = run_one(sequential_command, args.project)
        print()
        print(
            "sequential check: %.2f s, exit %d"
            % (sequential["elapsed"], sequential["code"])
        )
        if sequential["code"] != 0:
            print(sequential["text"].rstrip())
            status = 1
        parallel_lines = []
        for record in records.values():
            parallel_lines.extend(record["diagnostics"])
        same_diagnostics = compare_diagnostics(
            parallel_lines, diagnostic_lines(sequential["text"])
        )
        same_cache = compare_caches(args.cache_dir, sequential_cache)
        if not same_diagnostics or not same_cache:
            status = 1
        if not blocked and wall > 0:
            print(
                "sequential / parallel wall time: %.2f s / %.2f s (%.2fx)"
                % (sequential["elapsed"], wall, sequential["elapsed"] / wall)
            )

    return status


if __name__ == "__main__":
    sys.exit(main())
