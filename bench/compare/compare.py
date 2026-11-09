"""Stitchwort against CPython, PyPy and Lean: check answers, then time.

Run through compare.sh (see README.md). Every runner of a program is run once
on its input and its standard output compared with expected.txt byte for
byte; only runners that match are timed, with hyperfine.
"""

import argparse
import datetime
import json
import math
import platform
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OUT = ROOT / "target" / "compare"

# Column order of the table. `js` and `jit` only run with --all.
RUNNERS = ["run", "native", "js", "jit", "cpython", "pypy", "lean", "lean-run"]
OPTIONAL = {"js", "jit"}

# `set` in programs.toml: the original ten programs are "core", the wider
# programs added to catch over-fitting to them are "wide". Their geometric
# means are reported apart so the core ten's history stays comparable.
SETS = ["core", "wide"]


def camel(name):
    return "".join(part.capitalize() for part in name.split("-"))


def scaled_input(name, entry):
    """Write the scaled copy of a program's `source` file, once per run, and
    return its path. `scale` says how the file grows by `repeat`:
      lines    the whole file, repeated
      messages the rules (text before the first blank line) once, the rest repeated
      join0    the one-line file repeated with "0" between copies
      tile     a grid of lines, repeated `repeat` times across and down
    """
    text = (ROOT / entry["source"]).read_text().strip("\n")
    repeat = entry["repeat"]
    scale = entry["scale"]
    if scale == "lines":
        out = "\n".join([text] * repeat)
    elif scale == "messages":
        rules, messages = text.split("\n\n")
        out = rules + "\n\n" + "\n".join([messages] * repeat)
    elif scale == "join0":
        out = "0".join([text] * repeat)
    elif scale == "tile":
        rows = [line * repeat for line in text.split("\n")]
        out = "\n".join(rows * repeat)
    else:
        raise ValueError(f"{name}: unknown scale {scale!r}")
    path = OUT / "inputs" / f"{name}.txt"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(out + "\n")
    return path


class Program:
    def __init__(self, name, entry):
        self.name = name
        if "source" in entry:
            self.input = scaled_input(name, entry)
        else:
            self.input = ROOT / entry["input"] if "input" in entry else None
        self.args = entry.get("args", [])
        self.set = entry.get("set", "core")
        if self.set not in SETS:
            raise ValueError(f"{name}: unknown set {self.set!r}; known: {', '.join(SETS)}")
        self.target = entry["stitchwort"]
        self.dir = HERE / name
        self.expected = (self.dir / "expected.txt").read_bytes()
        self.is_file = self.target.endswith(".sw")
        self.python = self.dir / "main.py"
        self.lean_exe = name.replace("-", "_")
        self.lean_file = HERE / "lean" / "Compare" / (camel(name) + ".lean")
        self.native_exe = OUT / "bin" / name

    def command(self, runner, sw):
        """The shell command for a runner, or None if the program has none."""
        args = " ".join(shlex.quote(a) for a in self.args)
        # `--` keeps the program's arguments from being read as options.
        sw_args = f"-- {args}" if args else ""
        if self.is_file:
            where, target = ROOT, shlex.quote(str(ROOT / self.target))
        else:
            where, target = ROOT / "aoc", shlex.quote(self.target)
        in_dir = f"cd {shlex.quote(str(where))} && "
        sw = shlex.quote(str(sw))
        if runner == "run":
            return f"{in_dir}{sw} run {target} {sw_args}"
        if runner == "js":
            return f"{in_dir}{sw} run --js {target} {sw_args}"
        if runner == "jit":
            return f"{in_dir}{sw} run --native {target} {sw_args}"
        if runner == "native":
            return f"{shlex.quote(str(self.native_exe))} {args}"
        if runner in ("cpython", "pypy"):
            if not self.python.exists():
                return None
            exe = "python3" if runner == "cpython" else "pypy3"
            return f"{exe} {shlex.quote(str(self.python))} {args}"
        if not self.lean_file.exists():
            return None
        if runner == "lean":
            exe = HERE / "lean" / ".lake" / "build" / "bin" / self.lean_exe
            return f"{shlex.quote(str(exe))} {args}"
        if runner == "lean-run":
            return f"lean --run {shlex.quote(str(self.lean_file))} {args}"
        raise ValueError(runner)

    def build_native(self, sw):
        """Build the native executable; returns (seconds, error or None)."""
        self.native_exe.parent.mkdir(parents=True, exist_ok=True)
        target = str(ROOT / self.target) if self.is_file else self.target
        cwd = ROOT if self.is_file else ROOT / "aoc"
        start = time.monotonic()
        done = subprocess.run(
            [str(sw), "build", "--native", target, "-o", str(self.native_exe)],
            cwd=cwd, capture_output=True, text=True,
        )
        seconds = time.monotonic() - start
        if done.returncode != 0:
            return seconds, (done.stderr or done.stdout).strip()[-400:]
        return seconds, None


def run_once(program, command):
    """(stdout bytes, seconds, return code, stderr tail) of one run."""
    stdin = open(program.input, "rb") if program.input else subprocess.DEVNULL
    start = time.monotonic()
    done = subprocess.run(command, shell=True, stdin=stdin, capture_output=True)
    seconds = time.monotonic() - start
    if program.input:
        stdin.close()
    return done.stdout, seconds, done.returncode, done.stderr.decode(errors="replace")[-300:]


def parse_instructions(text, system):
    """Instructions retired from a tool's stderr, or None.

    macOS `/usr/bin/time -l` prints "  123456  instructions retired".
    Linux `perf stat -x,` prints "123456,,instructions,..." (the count is
    "<not counted>" or "<not supported>" when the kernel won't say).
    """
    for line in text.splitlines():
        if system == "Darwin" and line.rstrip().endswith("instructions retired"):
            digits = line.split()[0]
            return int(digits) if digits.isdigit() else None
        if system == "Linux":
            fields = line.split(",")
            if len(fields) > 2 and fields[0].strip().isdigit() and fields[2].startswith("instructions"):
                return int(fields[0])
    return None


def instructions_wrapper(system):
    """The argv prefix that reports instructions retired, or None if this
    machine can't (no `perf` on Linux, or another OS)."""
    if system == "Darwin" and Path("/usr/bin/time").exists():
        return ["/usr/bin/time", "-l"]
    if system == "Linux" and have("perf"):
        return ["perf", "stat", "-e", "instructions", "-x,"]
    return None


def count_instructions(program, command):
    """Instructions retired by one run of a command (children included), or
    None. Run apart from hyperfine, once, since the count is stable."""
    system = platform.system()
    wrapper = instructions_wrapper(system)
    if wrapper is None:
        return None
    stdin = open(program.input, "rb") if program.input else subprocess.DEVNULL
    try:
        done = subprocess.run(wrapper + ["sh", "-c", command], stdin=stdin, capture_output=True)
    finally:
        if program.input:
            stdin.close()
    return parse_instructions(done.stderr.decode(errors="replace"), system)


def geomean(values):
    return math.exp(sum(math.log(v) for v in values) / len(values))


def geomean_lines(ratios, sets):
    """Markdown rows of the geometric mean of native/CPython and native/Lean
    over the core programs, the wide ones, and all. `ratios` is
    {program: {"cpython": x, "lean": y}} (a pair missing where a runner was
    skipped or failed), `sets` {program: "core" or "wide"}. A mean covers the
    programs that have the pair, and the row says how many."""
    lines = ["| Geometric mean | native / CPython | native / Lean |", "|---|---:|---:|"]
    groups = [("core", ["core"]), ("wide", ["wide"]), ("all", SETS)]
    for label, members in groups:
        cells = []
        for pair in ("cpython", "lean"):
            values = [r[pair] for n, r in ratios.items() if sets[n] in members and pair in r]
            cells.append(f"{geomean(values):.2f}x ({len(values)} programs)" if values else "-")
        lines.append("| " + " | ".join([label] + cells) + " |")
    return "\n".join(lines)


def fmt_count(n):
    if n is None:
        return "n/a"
    for unit, size in (("G", 1e9), ("M", 1e6), ("k", 1e3)):
        if n >= size:
            return f"{n / size:.2f} {unit}"
    return str(n)


def instruction_table(counts, order, shown):
    """(markdown rows, ratios) of instructions retired net of the null
    program's, with the same ratios as the time table."""
    ratios = {}
    startup = counts.get("null", {})
    head = ["Program (instructions)"] + shown + ["run / CPython", "native / CPython", "native / Lean"]
    lines = ["| " + " | ".join(head) + " |", "|---|" + "---:|" * (len(head) - 1)]
    for name in order:
        cells, net = [], {}
        for runner in shown:
            n = counts[name].get(runner)
            if n is None:
                cells.append("n/a" if runner in counts[name] else "-")
                continue
            net[runner] = max(n - (startup.get(runner) or 0), 0)
            cells.append(fmt_count(net[runner]))

        def ratio(a, b):
            if a in net and b in net and net[b] > 0:
                return f"{net[a] / net[b]:.2f}x"
            return "-"

        ratios[name] = pair_ratios(net)
        lines.append("| " + " | ".join([name] + cells + [ratio("run", "cpython"), ratio("native", "cpython"), ratio("native", "lean")]) + " |")
    lines.append("| " + " | ".join(["startup"] + [fmt_count(startup.get(r)) if r in startup else "-" for r in shown] + ["", "", ""]) + " |")
    return "\n".join(lines), ratios


def pair_ratios(net):
    """The headline ratios of one program's net values, where both exist."""
    return {
        pair: net["native"] / net[pair]
        for pair in ("cpython", "lean")
        if "native" in net and pair in net and net[pair] > 0
    }


def have(tool):
    return shutil.which(tool) is not None


def build_lean(programs, built):
    lean_dir = HERE / "lean"
    if not (have("lake") and any(p.lean_file.exists() for p in programs)):
        return None, "lake not on PATH" if not have("lake") else None
    exes = [p.lean_exe for p in programs if p.lean_file.exists()]
    start = time.monotonic()
    done = subprocess.run(["lake", "build", *exes], cwd=lean_dir, capture_output=True, text=True)
    seconds = time.monotonic() - start
    if done.returncode != 0:
        return seconds, "lake build failed: " + (done.stderr or done.stdout).strip()[-400:]
    built["lean"] = seconds
    return seconds, None


def check_all(programs, runners, sw):
    """Run every runner once; returns {(program, runner): (status, seconds, note)}."""
    results = {}
    builds = {}
    lean_seconds, lean_error = build_lean(programs, builds)
    for program in programs:
        for runner in runners:
            command = program.command(runner, sw)
            key = (program.name, runner)
            if command is None:
                results[key] = ("SKIP", 0, "no port")
                continue
            line = lambda: print(f"  {program.name:14} {runner:9} {results[key][0]:5} {results[key][1]:7.2f} s  {results[key][2]}", flush=True)
            tool = {"cpython": "python3", "pypy": "pypy3", "lean-run": "lean"}.get(runner)
            if tool and not have(tool):
                results[key] = ("SKIP", 0, f"{tool} not on PATH")
                line()
                continue
            if runner == "lean" and lean_error:
                results[key] = ("FAIL", 0, lean_error)
                line()
                continue
            if runner == "native":
                seconds, error = program.build_native(sw)
                if error:
                    results[key] = ("FAIL", seconds, "native build failed: " + error)
                    line()
                    continue
                builds[f"native:{program.name}"] = seconds
            stdout, seconds, code, stderr = run_once(program, command)
            if code != 0:
                results[key] = ("FAIL", seconds, f"exit {code}: {stderr.strip()}")
            elif stdout != program.expected:
                results[key] = ("FAIL", seconds, "output differs from expected.txt")
            else:
                results[key] = ("ok", seconds, "")
            line()
    return results, builds


def hyperfine(program, runners, runs, scratch):
    """Time the runners of one program; {runner: hyperfine's result dict}."""
    json_path = scratch / f"{program.name}.json"
    cmd = ["hyperfine", "--warmup", "1", "--runs", str(runs), "--export-json", str(json_path)]
    cmd += ["--input", str(program.input)] if program.input else ["--input", "null"]
    for runner in runners:
        cmd += ["--command-name", runner, program.command(runner, SW[0])]
    subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL)
    return {r["command"]: r for r in json.loads(json_path.read_text())["results"]}


def fmt(seconds):
    if seconds is None:
        return "-"
    if seconds < 1:
        return f"{seconds * 1000:.0f} ms"
    return f"{seconds:.2f} s"


def table(timings, startup, order, shown):
    """(markdown rows, ratios): medians net of startup, ratios, and a * on wide spreads."""
    ratios = {}
    head = ["Program"] + shown + ["run / CPython", "native / CPython", "native / Lean"]
    lines = ["| " + " | ".join(head) + " |", "|---|" + "---:|" * (len(head) - 1)]
    for name in order:
        cells, net = [], {}
        for runner in shown:
            result = timings[name].get(runner)
            if result is None:
                cells.append("-")
                continue
            base = startup.get(runner, 0.0)
            value = max(result["median"] - base, 0.0)
            net[runner] = value
            spread = (result["max"] - result["min"]) / result["median"] if result["median"] else 0
            cells.append(fmt(value) + (" *" if spread > 0.05 else ""))

        def ratio(a, b):
            if a in net and b in net and net[b] > 0:
                return f"{net[a] / net[b]:.2f}x"
            return "-"

        ratios[name] = pair_ratios(net)
        lines.append("| " + " | ".join([name] + cells + [ratio("run", "cpython"), ratio("native", "cpython"), ratio("native", "lean")]) + " |")
    start = ["startup"] + [fmt(startup.get(r)) for r in shown] + ["", "", ""]
    lines.append("| " + " | ".join(start) + " |")
    return "\n".join(lines), ratios


SW = [None]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--sw", required=True, type=Path, help="the stitchwort binary (with the native feature)")
    parser.add_argument("--check", action="store_true", help="only check the answers, don't time")
    parser.add_argument("--runs", type=int, default=5, help="hyperfine runs per command (3 for anything over 30 s)")
    parser.add_argument("--all", action="store_true", help="also time run --js and run --native (the JIT)")
    parser.add_argument("--instructions", action="store_true", help="also report instructions retired, one run per program and runner after timing (macOS /usr/bin/time -l, Linux perf stat); steadier than wall time on a busy machine")
    parser.add_argument("--runners", help="comma-separated runners to use, e.g. native,cpython,pypy,lean (default: all but js and jit)")
    parser.add_argument("names", nargs="*", help="programs to run (default: all)")
    opts = parser.parse_args()
    SW[0] = opts.sw.resolve()

    config = tomllib.loads((HERE / "programs.toml").read_text())
    unknown = [n for n in opts.names if n not in config]
    if unknown:
        sys.exit(f"unknown program(s) {unknown}; known: {', '.join(config)}")
    names = opts.names or list(config)
    # The null program goes first and is always run: it is the startup row.
    names = ["null"] + [n for n in names if n != "null"]
    programs = [Program(n, config[n]) for n in names]
    runners = [r for r in RUNNERS if opts.all or r not in OPTIONAL]
    if opts.runners:
        wanted = opts.runners.split(",")
        bad = [r for r in wanted if r not in RUNNERS]
        if bad:
            sys.exit(f"unknown runner(s) {bad}; known: {', '.join(RUNNERS)}")
        runners = [r for r in RUNNERS if r in wanted]

    print("Checking answers against expected.txt:")
    results, builds = check_all(programs, runners, SW[0])
    failed = [k for k, v in results.items() if v[0] == "FAIL"]
    print(f"{sum(v[0] == 'ok' for v in results.values())} ok, "
          f"{sum(v[0] == 'SKIP' for v in results.values())} skipped, {len(failed)} failed")
    if opts.check:
        sys.exit(1 if failed else 0)

    if not have("hyperfine"):
        sys.exit("hyperfine is not on PATH: run inside `nix develop .#compare`")
    OUT.mkdir(parents=True, exist_ok=True)
    timings = {}
    counts = {}
    with tempfile.TemporaryDirectory() as scratch:
        for program in programs:
            ok = [r for r in runners if results[(program.name, r)][0] == "ok"]
            wrong = [r for r in runners if results[(program.name, r)][0] == "FAIL"]
            if wrong:
                print(f"{program.name}: not timing {', '.join(wrong)} (wrong answer or failed)")
            timings[program.name] = {}
            for runner in ok:
                # One hyperfine call per runner: a slow one gets fewer runs.
                runs = 3 if results[(program.name, runner)][1] > 30 else opts.runs
                print(f"timing {program.name} / {runner} ({runs} runs)", flush=True)
                timings[program.name].update(hyperfine(program, [runner], runs, Path(scratch)))
                if opts.instructions:
                    counts.setdefault(program.name, {})[runner] = count_instructions(program, program.command(runner, SW[0]))

    startup = {r: t["median"] for r, t in timings["null"].items()}
    shown = [r for r in runners if any(r in timings[n] for n in timings)]
    order = [n for n in names if n != "null"]
    sets = {p.name: p.set for p in programs}
    md, time_ratios = table(timings, startup, order, shown)
    md += "\n\n" + geomean_lines(time_ratios, sets)
    if opts.instructions:
        if instructions_wrapper(platform.system()) is None:
            md += "\n\nInstructions retired: n/a (needs macOS /usr/bin/time or Linux perf)"
        else:
            rows, instruction_ratios = instruction_table(counts, order, shown)
            md += "\n\n" + rows + "\n\n" + geomean_lines(instruction_ratios, sets)
    if builds:
        md += "\n\nBuild times (not in the run times): " + ", ".join(f"{k} {v:.1f} s" for k, v in builds.items())
    if failed:
        md += "\n\nNot timed: " + ", ".join(f"{p}/{r}" for p, r in failed)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H%M%S") + "-" + platform.node().split(".")[0]
    versions = {}
    for tool, flag in [("python3", "--version"), ("pypy3", "--version"), ("lean", "--version"), ("hyperfine", "--version")]:
        if have(tool):
            versions[tool] = subprocess.run([tool, flag], capture_output=True, text=True).stdout.strip().splitlines()[0]
    commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    meta = {"commit": commit, "host": platform.node(), "versions": versions, "load": list(__import__("os").getloadavg()), "builds": builds}
    if opts.instructions:
        meta["instructions_note"] = "instructions retired by one run, startup not subtracted"
    (OUT / f"{stamp}.json").write_text(json.dumps({"meta": meta, "timings": timings, **({"instructions": counts} if opts.instructions else {})}, indent=1))
    (OUT / f"{stamp}.md").write_text(md + "\n")
    print()
    print(md)
    print(f"\nWrote {OUT / (stamp + '.json')} and .md")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
