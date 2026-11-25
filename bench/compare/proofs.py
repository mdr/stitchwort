"""Checking speed: Stitchwort against Lean on three AoC days' proofs.

Run through `task bench:compare:proofs` (inside `nix develop .#compare`, on a
binary built without the dev features); see bench/compare/lean-proofs/README.md
and docs/proposals/comparative-speed.md section 3. For each day:

  sw       `stitchwort check --no-cache <the day's namespaces> --only <the theorems
           the Lean file has>`, from aoc/ (SW-2310: the same theorems Lean checks,
           and what they need; the Lean file's theorem names pick them), hyperfine
           wall time: everything cold, the library rechecked from source
  sw net   the elaboration plus kernel time of the day's own units (the rows of
           `--timings=all`'s unit table that are neither `core` nor `std/...`), a
           median over the same number of runs of the same command as the others.
           Counts only the day's own namespaces, whatever library files the day
           pulls in (SW-4810: a probe file never loaded the same std files the day
           did, so a difference of wall times charged the library files the probe
           missed to the day)
  sw cached  `check --no-project-cache` of the same namespaces, the library
           cache warmed first (hyperfine's untimed warmup run): the whole run with
           the library precompiled, our counterpart of Lean's `.olean` files
  sw floor  `check` of the day's namespaces (no --only), every cache warm, one job
           (STITCHWORT_JOBS=1) and with the default jobs (STITCHWORT_JOBS unset):
           nothing to check, the cost of every check after an edit elsewhere
           (SW-4818). --only and --no-project-cache both force one job, so the
           default-jobs row can only be this one
  lean     `lean Proofs/<Day>.lean`, Lib already built (the day's file alone)
  lean-load `lean` on a file that only imports Lib
  lake     a cold `lake build <Day>` (.lake deleted first): Lib and the day
"""

import argparse
import datetime
import json
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OUT = ROOT / "target" / "compare"
LEAN = HERE / "lean-proofs"

DAYS = {
    "2024-day02": {
        "namespaces": ["Aoc.Year2024.Day02.Proofs"],
        "module": "Day2024_02",
    },
    "2020-day18": {
        "namespaces": ["Aoc.Year2020.Day18.Proofs"],
        "module": "Day2020_18",
    },
    "2021-day15": {
        "namespaces": ["Aoc.Year2021.Day15.Proofs", "Aoc.Common.Proofs"],
        "module": "Day2021_15",
    },
}


THEOREM = re.compile(r"^(?:protected |private )?(?:theorem|lemma)\s+([^\s(:\[{]+)", re.M)


def lean_theorem_names(module):
    """The last segments of the theorem names in the day's Lean file."""
    text = (LEAN / "Proofs" / f"{module}.lean").read_text()
    return {name.rsplit(".", 1)[-1] for name in THEOREM.findall(text)}


def ported_theorems(day):
    """The full names of the day's Stitchwort theorems that its Lean file also
    has (same name), in the day's namespaces."""
    wanted = lean_theorem_names(day["module"])
    found = []
    for path in sorted((ROOT / "aoc" / "src").rglob("*.sw")):
        text = path.read_text()
        header = re.search(r"^namespace\s+(\S+)", text, re.M)
        if not header or header.group(1) not in day["namespaces"]:
            continue
        for name in re.findall(r"^theorem\s+([^\s(:\[{]+)", text, re.M):
            if name.rsplit(".", 1)[-1] in wanted:
                found.append(f"{header.group(1)}.{name}")
    return found


class Runs:
    """The timed runs of one command: wall times and hyperfine's CPU times."""

    def __init__(self, wall, user, system):
        self.wall = wall
        self.user = user  # mean user CPU seconds, or None
        self.system = system  # mean system CPU seconds, or None

    @property
    def median(self):
        return statistics.median(self.wall)

    @property
    def lo(self):
        return min(self.wall)

    @property
    def hi(self):
        return max(self.wall)


def hyperfine(name, command, runs, scratch, prepare=None, cwd=None, env=None):
    """The wall times (and mean user and system CPU seconds) of `runs` timed
    runs, after one untimed warmup. Reads either JSON format: hyperfine 2.0's
    `measurements[]` (`time_wall_clock.value`, and `time_user`/`time_system` if
    present) or 1.x's `times`, `user`, `system` (the flake's is 1.21; its user and
    system are means over the runs). Neither wall form present, or a wrong run
    count, stops the bench."""
    json_path = scratch / f"{name}.json"
    cmd = ["hyperfine", "--warmup", "1", "--runs", str(runs), "--export-json", str(json_path),
           "--command-name", name, "--input", "null"]
    if prepare:
        cmd += ["--prepare", prepare]
    cmd.append(command)
    done = subprocess.run(cmd, cwd=cwd, env=env, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if done.returncode != 0:
        sys.exit(f"hyperfine failed on {name}: {done.stderr[-400:]}")
    try:
        result = json.loads(json_path.read_text())["results"][0]
        if "measurements" in result:
            times = [m["time_wall_clock"]["value"] for m in result["measurements"]]
            users = [m["time_user"]["value"] for m in result["measurements"] if "time_user" in m]
            systems = [m["time_system"]["value"] for m in result["measurements"] if "time_system" in m]
            user = statistics.mean(users) if users else None
            system = statistics.mean(systems) if systems else None
        else:
            times = result["times"]
            user, system = result.get("user"), result.get("system")
    except (KeyError, IndexError, TypeError) as err:
        sys.exit(f"hyperfine's JSON for {name} lacks the expected key {err}: has this version's format changed?")
    if len(times) != runs:
        sys.exit(f"hyperfine's JSON for {name} has {len(times)} measurements, expected {runs}")
    return Runs(times, user, system)


def own_net_seconds(sw, day, only):
    """(all, common): elaboration plus kernel seconds of the day's own units from
    one `--timings=all` run, and the part of them in `Aoc.Common...` units. The
    unit table's rows that are neither `core`, the `library files` summary nor a
    `std/...` file (the day's namespaces, and project namespaces they use)."""
    done = subprocess.run([sw, "check", "--no-cache", *day["namespaces"], "--only", only, "--timings=all"],
                          cwd=ROOT / "aoc", capture_output=True, text=True)
    if done.returncode != 0:
        sys.exit("check with --timings failed:\n" + (done.stdout + done.stderr)[-800:])
    lines = (done.stdout + done.stderr).splitlines()
    starts = [i for i, line in enumerate(lines) if line.startswith("unit ") and "elab ms" in line]
    if not starts:
        sys.exit("--timings=all printed no unit table: " + (done.stdout + done.stderr)[-400:])
    total = 0.0
    common = 0.0
    rows = 0
    for line in lines[starts[0] + 1:]:
        if line.startswith("total"):
            break
        fields = line.split()
        if len(fields) < 5 or fields[0] in ("core", "library") or fields[0].startswith("std/"):
            continue
        ms = float(fields[-4]) + float(fields[-3])
        total += ms
        if fields[0].startswith("Aoc.Common"):
            common += ms
        rows += 1
    if rows == 0:
        sys.exit("no project unit in the --timings table (the format changed?)")
    return total / 1000, common / 1000


def fmt(seconds):
    if seconds is None:
        return "-"
    return f"{seconds * 1000:.0f} ms" if seconds < 1 else f"{seconds:.2f} s"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sw", required=True, type=Path)
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("names", nargs="*", help=f"days (default: all of {', '.join(DAYS)})")
    opts = parser.parse_args()
    sw = str(opts.sw.resolve())
    names = opts.names or list(DAYS)
    unknown = [n for n in names if n not in DAYS]
    if unknown:
        sys.exit(f"unknown day(s) {unknown}; known: {', '.join(DAYS)}")
    for tool in ("hyperfine", "lake", "lean"):
        if not shutil.which(tool):
            sys.exit(f"{tool} is not on PATH: run inside `nix develop .#compare`")

    # Correctness first: Lean's package must build with no `sorry`.
    shutil.rmtree(LEAN / ".lake", ignore_errors=True)
    built = subprocess.run(["lake", "build"], cwd=LEAN, capture_output=True, text=True)
    text = built.stdout + built.stderr
    if built.returncode != 0 or "sorry" in text:
        sys.exit("lean-proofs does not build cleanly:\n" + text[-1500:])
    lean_path = str(LEAN / ".lake" / "build" / "lib" / "lean")

    rows = {}
    plain_env = {k: v for k, v in os.environ.items() if k != "STITCHWORT_JOBS"}
    one_job_env = {**plain_env, "STITCHWORT_JOBS": "1"}
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        (scratch / "empty.lean").write_text("import Lib\n")
        env_lean = f"LEAN_PATH={lean_path} lean"
        lean_load = hyperfine("lean-load", f"{env_lean} {scratch / 'empty.lean'}", opts.runs, scratch)
        for name in names:
            day = DAYS[name]
            row = {"lean-load": lean_load}
            ported = ported_theorems(day)
            if not ported:
                sys.exit(f"{name}: no theorem of the Lean file found in {day['namespaces']}")
            print(f"{name}: {len(ported)} theorems in common with the Lean file; stitchwort", flush=True)
            only = ",".join(ported)
            spaces = " ".join(day["namespaces"])
            row["sw"] = hyperfine(f"sw-{name}", f"{sw} check --no-cache {spaces} --only {only}",
                                  opts.runs, scratch, cwd=ROOT / "aoc", env=plain_env)
            nets = [own_net_seconds(sw, day, only) for _ in range(opts.runs)]
            row["sw-net"] = [n[0] for n in nets]
            row["sw-net-common"] = [n[1] for n in nets]
            # The warmup run fills the library cache, so every timed run loads the library from it.
            row["sw-cached"] = hyperfine(f"sw-cached-{name}", f"{sw} check --no-project-cache {spaces} --only {only}",
                                         opts.runs, scratch, cwd=ROOT / "aoc", env=plain_env)
            # Every cache warm and nothing changed: the warmup run fills them (and, with several
            # jobs, records that the check completed, so the timed runs skip the fill).
            row["floor-1"] = hyperfine(f"floor1-{name}", f"{sw} check {spaces}", opts.runs, scratch,
                                       cwd=ROOT / "aoc", env=one_job_env)
            row["floor-auto"] = hyperfine(f"floor-auto-{name}", f"{sw} check {spaces}", opts.runs, scratch,
                                          cwd=ROOT / "aoc", env=plain_env)
            row["theorems"] = len(ported)
            print(f"{name}: lean", flush=True)
            row["lean"] = hyperfine(f"lean-{name}", f"{env_lean} {LEAN / 'Proofs' / (day['module'] + '.lean')}", opts.runs, scratch)
            row["lake"] = hyperfine(f"lake-{name}", f"lake build {day['module']}", opts.runs, scratch,
                                    prepare="rm -rf .lake", cwd=LEAN)
            rows[name] = row

    def spread(values):
        return f"{fmt(statistics.median(values))} ({fmt(min(values))}-{fmt(max(values))})"

    def span(runs):
        return f"{fmt(runs.median)} ({fmt(runs.lo)}-{fmt(runs.hi)})"

    def ratio_range(top, bottom):
        """top / bottom as `median (min-max)`, the range from the smallest top over the
        largest bottom to the largest top over the smallest bottom; top and bottom are
        lists of seconds."""
        if min(bottom) <= 0:
            return "-"
        return (f"{statistics.median(top) / statistics.median(bottom):.2f}x "
                f"({min(top) / max(bottom):.2f}-{max(top) / min(bottom):.2f}x)")

    def lean_net_list(r):
        """The lean file's runs less the empty file's, every pairing's extremes and the
        medians' difference in the middle: [lowest, median difference, highest]."""
        lo = r["lean"].lo - r["lean-load"].hi
        mid = r["lean"].median - r["lean-load"].median
        hi = r["lean"].hi - r["lean-load"].lo
        return [max(lo, 1e-6), max(mid, 1e-6), max(hi, 1e-6)]

    def cpu(runs):
        if runs.user is None:
            return "-"
        return f"{fmt(runs.user)} + {fmt(runs.system)}"

    head1 = ["Day", "theorems", "sw check (cold)", "sw net", "of it Aoc.Common", "lean file", "lean load",
             "lean net", "sw net / lean net"]
    head2 = ["Day", "sw cached, one job", "(that) / lean file", "sw floor, one job", "sw floor, default jobs",
             "lake build (cold, with Lib)"]
    head3 = ["Day", "sw cached: wall", "user + system", "lean file: wall", "user + system", "lean load: wall",
             "user + system", "sw floor (default jobs): wall", "user + system"]

    def table(head, body):
        return ["| " + " | ".join(head) + " |", "|---|" + "---:|" * (len(head) - 1)] + \
               ["| " + " | ".join(line) + " |" for line in body]

    body1, body2, body3 = [], [], []
    for name, r in rows.items():
        net = lean_net_list(r)
        lean_net = f"{fmt(net[1])} ({fmt(net[0])}-{fmt(net[2])})"
        common = spread(r["sw-net-common"]) if any(r["sw-net-common"]) else "-"
        body1.append([name, str(r["theorems"]), span(r["sw"]), spread(r["sw-net"]), common, span(r["lean"]),
                      span(r["lean-load"]), lean_net, ratio_range(r["sw-net"], net)])
        body2.append([name, span(r["sw-cached"]),
                      ratio_range(r["sw-cached"].wall, r["lean"].wall),
                      span(r["floor-1"]), span(r["floor-auto"]), span(r["lake"])])
        body3.append([name, fmt(r["sw-cached"].median), cpu(r["sw-cached"]), fmt(r["lean"].median), cpu(r["lean"]),
                      fmt(r["lean-load"].median), cpu(r["lean-load"]), fmt(r["floor-auto"].median),
                      cpu(r["floor-auto"])])
    md = "\n".join(table(head1, body1) + [""] + table(head2, body2) + [""] + table(head3, body3))
    raw = {name: {k: (v.__dict__ if isinstance(v, Runs) else v) for k, v in r.items()} for name, r in rows.items()}
    OUT.mkdir(parents=True, exist_ok=True)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H%M%S") + "-" + platform.node().split(".")[0]
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    meta = {"commit": commit, "host": platform.node(), "runs": opts.runs,
            "lean": subprocess.run(["lean", "--version"], capture_output=True, text=True).stdout.strip(),
            "load": list(__import__("os").getloadavg())}
    (OUT / f"{stamp}-proofs.json").write_text(json.dumps({"meta": meta, "rows": raw}, indent=1))
    (OUT / f"{stamp}-proofs.md").write_text(md + "\n")
    print()
    print(md)


main()
