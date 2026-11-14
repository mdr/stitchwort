"""Instructions retired by the native executables of bench/compare programs,
repeated, for before/after comparisons of a performance change.

Run through `task bench:instructions` (see README.md), which builds the
stitchwort binary and runtime non-incrementally first. Each program is built
natively once, then run N times; every run's output must equal expected.txt.
Wall time is not measured: instruction counts barely move with machine load,
so a change of a percent or two shows up, which hyperfine cannot see.
"""

import argparse
import importlib.util
import json
import platform
import statistics
import sys
import tomllib
from pathlib import Path

# Load compare.py by path: under `python3 -I` the script's directory is not on
# sys.path.
_spec = importlib.util.spec_from_file_location("compare", Path(__file__).resolve().parent / "compare.py")
compare = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(compare)

SAVE_DIR = compare.ROOT / "target" / "bench" / "instructions"


def summarise(counts):
    """min / median / max and spread ((max - min) / median) of one program's counts."""
    median = statistics.median(counts)
    return {
        "min": min(counts),
        "median": median,
        "max": max(counts),
        "spread": (max(counts) - min(counts)) / median if median else 0.0,
        "runs": len(counts),
    }


def compare_runs(current, saved):
    """Per-program change of the medians, in percent, for programs in both
    runs, and the geometric mean of the median ratios (as a percent change),
    or None when no program is in both. `current` and `saved` map program
    to summarise()'s dict."""
    changes = {
        name: (current[name]["median"] / saved[name]["median"] - 1) * 100
        for name in current
        if name in saved and saved[name]["median"] > 0 and current[name]["median"] > 0
    }
    if not changes:
        return changes, None
    mean = compare.geomean([1 + c / 100 for c in changes.values()])
    return changes, (mean - 1) * 100


def render(current, saved=None, against=None):
    """The report table as text."""
    changes, mean = compare_runs(current, saved) if saved is not None else ({}, None)
    head = ["Program", "min", "median", "max", "spread"] + ([f"vs {against}"] if saved is not None else [])
    rows = [head]
    for name, s in current.items():
        row = [name, compare.fmt_count(s["min"]), compare.fmt_count(s["median"]), compare.fmt_count(s["max"]), f"{s['spread'] * 100:.2f}%"]
        if saved is not None:
            row.append(f"{changes[name]:+.2f}%" if name in changes else "-")
        rows.append(row)
    widths = [max(len(r[i]) for r in rows) for i in range(len(head))]
    lines = ["  ".join(c.ljust(w) if i == 0 else c.rjust(w) for i, (c, w) in enumerate(zip(r, widths))) for r in rows]
    if saved is not None:
        lines.append(f"geomean change of medians vs {against}: " + (f"{mean:+.2f}% ({len(changes)} programs)" if mean is not None else "n/a"))
    return "\n".join(lines)


def measure(program, runs):
    """(counts, error): the instruction counts of `runs` runs, or an error
    message for the first run that fails, prints the wrong answer or yields
    no count."""
    command = program.command("native", None)
    counts = []
    for i in range(runs):
        count, stdout, code = compare.run_counted(program, command)
        if code != 0:
            return None, f"run {i + 1} exited {code}"
        if stdout != program.expected:
            return None, f"run {i + 1} output differs from expected.txt"
        if count is None:
            return None, f"run {i + 1} gave no instruction count"
        counts.append(count)
    return counts, None


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--sw", required=True, type=Path, help="the stitchwort binary (with the native feature)")
    parser.add_argument("--runs", type=int, default=5, help="runs per program (default 5)")
    parser.add_argument("--set", choices=compare.SETS, help="only the core or the wide programs")
    parser.add_argument("--save", metavar="NAME", help=f"write the result to {SAVE_DIR.relative_to(compare.ROOT)}/NAME.json")
    parser.add_argument("--against", metavar="NAME", help="compare the medians with a saved run")
    parser.add_argument("names", nargs="*", help="programs to run (default: all but null)")
    opts = parser.parse_args()
    if opts.runs < 1:
        sys.exit("--runs must be at least 1")
    if compare.instructions_wrapper(platform.system()) is None:
        sys.exit("no instruction counter: needs macOS /usr/bin/time or Linux perf")
    saved = None
    if opts.against:
        path = SAVE_DIR / f"{opts.against}.json"
        if not path.exists():
            sys.exit(f"no saved run {path}")
        saved = json.loads(path.read_text())["programs"]

    config = tomllib.loads((compare.HERE / "programs.toml").read_text())
    unknown = [n for n in opts.names if n not in config]
    if unknown:
        sys.exit(f"unknown program(s) {unknown}; known: {', '.join(config)}")
    names = opts.names or [n for n in config if n != "null" and (not opts.set or config[n].get("set", "core") == opts.set)]
    sw = opts.sw.resolve()

    current, failed = {}, []
    for name in names:
        program = compare.Program(name, config[name])
        seconds, error = program.build_native(sw)
        if error:
            failed.append(f"{name}: native build failed: {error}")
            continue
        print(f"{name}: built in {seconds:.1f} s, {opts.runs} runs", flush=True)
        counts, error = measure(program, opts.runs)
        if error:
            failed.append(f"{name}: {error}")
            continue
        current[name] = summarise(counts)

    print()
    if current:
        print(render(current, saved, opts.against))
    for line in failed:
        print("FAILED " + line)
    if opts.save and current:
        SAVE_DIR.mkdir(parents=True, exist_ok=True)
        commit = compare.subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=compare.ROOT, capture_output=True, text=True).stdout.strip()
        (SAVE_DIR / f"{opts.save}.json").write_text(json.dumps({"commit": commit, "host": platform.node(), "programs": current}, indent=1))
        print(f"\nSaved {SAVE_DIR / (opts.save + '.json')}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
