"""Checking speed: Stitchwort against Lean on three AoC days' proofs.

Run through `task bench:compare:proofs` (inside `nix develop .#compare`); see
bench/compare/lean-proofs/README.md and docs/proposals/comparative-speed.md
section 3. For each day it times, with hyperfine:

  sw       `stitchwort check --no-cache <the day's namespaces> --only <the theorems
           the Lean file has>`, from aoc/ (SW-2310: the same theorems Lean checks,
           and what they need; the Lean file's theorem names pick them)
  sw-load  `stitchwort check --no-cache` of a file that imports what the day imports
           from Std and uses its heavy parts (the library Lean has prebuilt in Lib)
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
        "imports": "Bool, Char, Eq, List, Nat, Parse",
        "probe": "def probe (read: List Char): Prop := read.all Parse.isDigit = True\n",
    },
    "2020-day18": {
        "namespaces": ["Aoc.Year2020.Day18.Proofs"],
        "module": "Day2020_18",
        "imports": "Bool, Char, DecEq, Eq, Exists, Fail, List, Nat, Option, Parse, Result, Text, Void",
        "probe": "def probe (p: () → {Parse} a) (spec: List Char → a → Prop) (read rest: List Char) (value: a): Prop :=\n"
        "  Parse.Reads p spec ∧ Parse.Runs p read rest value\n",
    },
    "2021-day15": {
        "namespaces": ["Aoc.Year2021.Day15.Proofs", "Aoc.Common.Proofs"],
        "module": "Day2021_15",
        "imports": "Bool, DecEq, Decidable, Eq, Exists, Fin, Graph, List, Map, Nat, Option, Ord, Quot, Void",
        "probe": "theorem probe [auto ord: Ord s] (graph: Graph s) (sources: List (s, Nat)):\n"
        "  Graph.Shortest graph sources (graph.distances sources) := Graph.distancesShortest graph sources\n",
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
    json_path = scratch / f"{name}.json"
    cmd = ["hyperfine", "--warmup", "1", "--runs", str(runs), "--export-json", str(json_path),
           "--command-name", name, "--input", "null"]
    if prepare:
        cmd += ["--prepare", prepare]
    cmd.append(command)
    done = subprocess.run(cmd, cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    if done.returncode != 0:
        sys.exit(f"hyperfine failed on {name}: {done.stderr[-400:]}")
    return json.loads(json_path.read_text())["results"][0]


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
            load_file = scratch / f"load-{name}.sw"
            # A name only loads (and checks) its Std module when something uses it, so
            # the probe uses the modules the day's proofs lean on; otherwise their
            # load lands in "sw net".
            load_file.write_text(f"namespace Load\nimport Std ({day['imports']})\n{day['probe']}")
            row = {"lean-load": lean_load["median"]}
            print(f"{name}: stitchwort", flush=True)
            row["sw-load"] = hyperfine(f"sw-load-{name}", f"{sw} check --no-cache {load_file}", opts.runs, scratch)["median"]
            ported = ported_theorems(day)
            if not ported:
                sys.exit(f"{name}: no theorem of the Lean file found in {day['namespaces']}")
            print(f"{name}: {len(ported)} theorems in common with the Lean file", flush=True)
            only = ",".join(ported)
            row["sw"] = hyperfine(f"sw-{name}", f"{sw} check --no-cache {' '.join(day['namespaces'])} --only {only}",
                                  opts.runs, scratch, cwd=ROOT / "aoc")["median"]
            row["theorems"] = len(ported)
            print(f"{name}: lean", flush=True)
            row["lean"] = hyperfine(f"lean-{name}", f"{env_lean} {LEAN / 'Proofs' / (day['module'] + '.lean')}",
                                    opts.runs, scratch)["median"]
            row["lake"] = hyperfine(f"lake-{name}", f"lake build {day['module']}", opts.runs, scratch,
                                    prepare="rm -rf .lake", cwd=LEAN)["median"]
            rows[name] = row

    head = ["Day", "theorems", "sw check", "sw load", "sw net", "lean file", "lean load", "lean net", "sw net / lean net", "lake build (cold, with Lib)"]
    lines = ["| " + " | ".join(head) + " |", "|---|" + "---:|" * (len(head) - 1)]
    for name, r in rows.items():
        sw_net = max(r["sw"] - r["sw-load"], 0.0)
        lean_net = max(r["lean"] - r["lean-load"], 0.0)
        ratio = f"{sw_net / lean_net:.2f}x" if lean_net > 0 else "-"
        lines.append("| " + " | ".join([name, str(r["theorems"]), fmt(r["sw"]), fmt(r["sw-load"]), fmt(sw_net), fmt(r["lean"]),
                                        fmt(r["lean-load"]), fmt(lean_net), ratio, fmt(r["lake"])]) + " |")
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
