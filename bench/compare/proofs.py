"""Checking speed: Stitchwort against Lean on three AoC days' proofs.

Run through `task bench:compare:proofs` (inside `nix develop .#compare`, on a
binary built without the dev features); see bench/compare/lean-proofs/README.md
and docs/proposals/comparative-speed.md section 3. For each day:

  sw       `stitchwort check --no-cache <the day's namespaces> --only <the theorems
           the Lean file has>`, from aoc/ (SW-2310: the same theorems Lean checks,
           and what they need; the Lean file's theorem names pick them), hyperfine
           wall time: everything cold, the library rechecked from source
  sw net   the elaboration plus kernel time of the day's own units (the rows of
           `--timings=all`'s unit table that are neither `core` nor `std/...`), one
           run of the same command. Counts only the day's own namespaces, whatever
           library files the day pulls in (SW-4810: a probe file never loaded the
           same std files the day did, so a difference of wall times charged the
           library files the probe missed to the day)
  sw cached  `check --no-project-cache` of the same namespaces, the library
           cache warmed first (hyperfine's untimed warmup run): the whole run with
           the library precompiled, our counterpart of Lean's `.olean` files
  lean     `lean Proofs/<Day>.lean`, Lib already built (the day's file alone)
  lean-load `lean` on a file that only imports Lib
  lake     a cold `lake build <Day>` (.lake deleted first): Lib and the day
"""

import argparse
import datetime
import json
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


def hyperfine(name, command, runs, scratch, prepare=None, cwd=None):
    """Median wall time in seconds. Reads either JSON format: hyperfine 2.0's
    `measurements[].time_wall_clock.value` (no `median`/`times` keys), or 1.x's
    `times` (the flake's is 1.21). Neither present, or a wrong run count,
    stops the bench."""
    json_path = scratch / f"{name}.json"
    cmd = ["hyperfine", "--warmup", "1", "--runs", str(runs), "--export-json", str(json_path),
           "--command-name", name, "--input", "null"]
    if prepare:
        cmd += ["--prepare", prepare]
    cmd.append(command)
    done = subprocess.run(cmd, cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if done.returncode != 0:
        sys.exit(f"hyperfine failed on {name}: {done.stderr[-400:]}")
    try:
        result = json.loads(json_path.read_text())["results"][0]
        if "measurements" in result:
            times = [m["time_wall_clock"]["value"] for m in result["measurements"]]
        else:
            times = result["times"]
    except (KeyError, IndexError, TypeError) as err:
        sys.exit(f"hyperfine's JSON for {name} lacks the expected key {err}: has this version's format changed?")
    if len(times) != runs:
        sys.exit(f"hyperfine's JSON for {name} has {len(times)} measurements, expected {runs}")
    return statistics.median(times)


def own_net_seconds(sw, day, only):
    """Elaboration plus kernel seconds of the day's own units, from one
    `--timings=all` run: the unit table's rows that are neither `core` nor a
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
    rows = 0
    for line in lines[starts[0] + 1:]:
        if line.startswith("total"):
            break
        fields = line.split()
        if len(fields) < 5 or fields[0] == "core" or fields[0].startswith("std/"):
            continue
        total += float(fields[-4]) + float(fields[-3])
        rows += 1
    if rows == 0:
        sys.exit("no project unit in the --timings table (the format changed?)")
    return total / 1000


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
                                  opts.runs, scratch, cwd=ROOT / "aoc")
            row["sw-net"] = own_net_seconds(sw, day, only)
            # The warmup run fills the library cache, so every timed run loads the library from it.
            row["sw-cached"] = hyperfine(f"sw-cached-{name}", f"{sw} check --no-project-cache {spaces} --only {only}",
                                         opts.runs, scratch, cwd=ROOT / "aoc")
            row["theorems"] = len(ported)
            print(f"{name}: lean", flush=True)
            row["lean"] = hyperfine(f"lean-{name}", f"{env_lean} {LEAN / 'Proofs' / (day['module'] + '.lean')}", opts.runs, scratch)
            row["lake"] = hyperfine(f"lake-{name}", f"lake build {day['module']}", opts.runs, scratch,
                                    prepare="rm -rf .lake", cwd=LEAN)
            rows[name] = row

    head = ["Day", "theorems", "sw check (cold)", "sw net", "lean file", "lean load", "lean net",
            "sw net / lean net", "sw check (library cached)", "(that) / lean file", "lake build (cold, with Lib)"]
    lines = ["| " + " | ".join(head) + " |", "|---|" + "---:|" * (len(head) - 1)]
    for name, r in rows.items():
        lean_net = max(r["lean"] - r["lean-load"], 0.0)
        ratio = f"{r['sw-net'] / lean_net:.2f}x" if lean_net > 0 else "-"
        lines.append("| " + " | ".join([name, str(r["theorems"]), fmt(r["sw"]), fmt(r["sw-net"]), fmt(r["lean"]),
                                        fmt(r["lean-load"]), fmt(lean_net), ratio, fmt(r["sw-cached"]),
                                        f"{r['sw-cached'] / r['lean']:.1f}x", fmt(r["lake"])]) + " |")
    md = "\n".join(lines)
    OUT.mkdir(parents=True, exist_ok=True)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H%M%S") + "-" + platform.node().split(".")[0]
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    meta = {"commit": commit, "host": platform.node(), "runs": opts.runs,
            "lean": subprocess.run(["lean", "--version"], capture_output=True, text=True).stdout.strip(),
            "load": list(__import__("os").getloadavg())}
    (OUT / f"{stamp}-proofs.json").write_text(json.dumps({"meta": meta, "rows": rows}, indent=1))
    (OUT / f"{stamp}-proofs.md").write_text(md + "\n")
    print()
    print(md)


main()
