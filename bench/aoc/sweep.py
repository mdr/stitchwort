"""Native speed over every Advent of Code day: `task bench:aoc`.

Builds each day's `main` natively, runs it on its committed puzzle input,
checks the output against the answers the test suite uses
(crates/cli/tests/running/aoc_answers.rs, read here, not copied), and records
instructions retired and wall time. Two runs can be compared per day, which
answers "did a speed change move anything outside the bench/compare ten?".
See README.md.
"""

import argparse
import datetime
import importlib.util
import json
import math
import os
import platform
import re
import signal
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OUT = ROOT / "target" / "bench-aoc"
ANSWERS_RS = ROOT / "crates" / "cli" / "tests" / "running" / "aoc_answers.rs"

# A day whose count differs from the old run's by more than this is flagged.
FLAG_PERCENT = 3.0

# Seconds a day's native build may take before it counts as a build failure.
BUILD_TIMEOUT = 120


def _load_compare():
    """bench/compare/compare.py, for its instructions-retired parser."""
    path = ROOT / "bench" / "compare" / "compare.py"
    spec = importlib.util.spec_from_file_location("compare", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


compare = _load_compare()


def rust_string(literal):
    """The value of the body of a Rust string literal: `\\n` is a newline and
    a backslash at a line's end drops the line break and the next line's
    leading blanks."""
    body = re.sub(r"\\\n\s*", "", literal)
    return body.replace("\\n", "\n")


def block(source, name):
    """The text of `const NAME: ... = &[ ... ];` in a Rust source."""
    match = re.search(r"const " + name + r"\b[^=]*=\s*&\[(.*?)\];", source, re.S)
    if not match:
        raise ValueError(f"{name} not found in {ANSWERS_RS}")
    return match.group(1)


def read_answers(source):
    """({(year, day): expected stdout}, set of (year, day) that are slow).

    The expected output is what `aoc_answers.rs` asserts: both parts, the
    second starting on a new line when it is a picture.
    """
    answers = {}
    string = r'"((?:[^"\\]|\\.)*)"'
    for fields in re.findall(r"\(\s*" + ",\\s*".join([string] * 4) + r"\s*,?\s*\)", block(source, "ANSWERS"), re.S):
        year, day, part1, part2 = (rust_string(f) for f in fields)
        sep = "\n" if "\n" in part2 else " "
        answers[(year, day)] = f"Part 1: {part1}\nPart 2:{sep}{part2}\n"
    slow = set(re.findall(r"\(" + string + r",\s*" + string + r"\)", block(source, "SLOW")))
    return answers, slow


def select(days, filter_text):
    """Days whose label ("2024/01") matches a FILTER: a bare year ("2024"),
    or a regex searched in the label."""
    if not filter_text:
        return days
    if re.fullmatch(r"\d{4}", filter_text):
        return [d for d in days if d[0] == filter_text]
    pattern = re.compile(filter_text)
    return [d for d in days if pattern.search(label(d))]


def label(day):
    return f"{day[0]}/{day[1]}"


def build(sw, day):
    """Build a day natively; returns (executable, seconds, error or None)."""
    year, number = day
    exe = OUT / "bin" / f"y{year}d{number}"
    exe.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    try:
        done = subprocess.run(
            [str(sw), "build", "--native", f"Aoc.Year{year}.Day{number}.main", "-o", str(exe)],
            cwd=ROOT / "aoc", capture_output=True, text=True, timeout=BUILD_TIMEOUT,
        )
    except subprocess.TimeoutExpired:
        return exe, time.monotonic() - start, f"build took over {BUILD_TIMEOUT} s"
    seconds = time.monotonic() - start
    if done.returncode != 0:
        return exe, seconds, (done.stderr or done.stdout).strip()[-400:]
    return exe, seconds, None


def run_day(exe, day, expected, timeout):
    """Run a built day on its input: a record with status, instructions, wall."""
    year, number = day
    wrapper = compare.instructions_wrapper(platform.system())
    argv = (wrapper or []) + [str(exe)]
    record = {"status": "ok", "instructions": None, "wall": None}
    with open(ROOT / "aoc" / "inputs" / year / f"day{number}.txt", "rb") as stdin:
        # Own process group, so a timeout kills the program and not just
        # the `time` wrapper in front of it.
        proc = subprocess.Popen(argv, stdin=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        start = time.monotonic()
        try:
            out, err = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.communicate()
            record["status"] = "timeout"
            record["wall"] = time.monotonic() - start
            return record
    record["wall"] = time.monotonic() - start
    record["instructions"] = compare.parse_instructions(err.decode(errors="replace"), platform.system()) if wrapper else None
    if proc.returncode != 0:
        record["status"] = "run-fail"
        record["detail"] = err.decode(errors="replace")[-300:]
    elif out.decode(errors="replace") != expected:
        record["status"] = "wrong"
        record["detail"] = out.decode(errors="replace")[-200:]
    return record


def measure(sw, day, expected, timeout):
    exe, build_seconds, error = build(sw, day)
    if error:
        return {"status": "build-fail", "instructions": None, "wall": None, "build": build_seconds, "detail": error}
    record = run_day(exe, day, expected, timeout)
    record["build"] = build_seconds
    return record


def fmt_count(n):
    if n is None:
        return "-"
    for unit, size in (("G", 1e9), ("M", 1e6), ("k", 1e3)):
        if n >= size:
            return f"{n / size:.2f} {unit}"
    return str(n)


def usable(record):
    """Whether a day's record is a measurement to compare."""
    return record is not None and record["status"] == "ok" and record.get("instructions")


def diff(new, old):
    """Per-day change of instructions between two runs' `days` maps.

    Returns (rows, geomean ratio or None): rows are (label, old, new, percent,
    flagged) for the days measured in both runs, in label order.
    """
    rows, ratios = [], []
    for name in sorted(new):
        if usable(new[name]) and usable(old.get(name)):
            before, after = old[name]["instructions"], new[name]["instructions"]
            percent = (after / before - 1) * 100
            rows.append((name, before, after, percent, abs(percent) > FLAG_PERCENT))
            ratios.append(after / before)
    mean = math.exp(sum(math.log(r) for r in ratios) / len(ratios)) if ratios else None
    return rows, mean


def table(days):
    lines = [f"{'day':<9}{'status':<11}{'instructions':>14}{'wall s':>9}{'build s':>9}"]
    for name in sorted(days):
        r = days[name]
        wall = "-" if r["wall"] is None else f"{r['wall']:.2f}"
        lines.append(f"{name:<9}{r['status']:<11}{fmt_count(r['instructions']):>14}{wall:>9}{r.get('build', 0):>9.1f}")
    return "\n".join(lines)


def diff_table(rows, mean, old_name):
    lines = [f"against {old_name}", f"{'day':<9}{'old':>14}{'new':>14}{'change':>9}"]
    for name, before, after, percent, flagged in rows:
        lines.append(f"{name:<9}{fmt_count(before):>14}{fmt_count(after):>14}{percent:>+8.2f}%{'  <-- moved' if flagged else ''}")
    if mean is None:
        lines.append("no day measured in both runs")
    else:
        lines.append(f"geomean of new/old instructions over {len(rows)} days: {mean:.4f} ({(mean - 1) * 100:+.2f}%)")
        moved = sum(1 for r in rows if r[4])
        lines.append(f"{moved} day(s) moved by more than {FLAG_PERCENT:g}%")
    return "\n".join(lines)


def previous_run(exclude):
    """The newest result file other than `exclude`, or None."""
    files = sorted(p for p in OUT.glob("*.json") if p != exclude)
    return files[-1] if files else None


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--sw", required=True, type=Path, help="the stitchwort binary (with the native feature)")
    parser.add_argument("--filter", help="a year (2024) or a regex searched in YEAR/DAY, e.g. '2024/0[1-3]'")
    parser.add_argument("--timeout", type=float, default=60, help="seconds per day's run (default 60)")
    parser.add_argument("-j", "--jobs", type=int, default=1, help="days in parallel (default 1; instruction counts may drift under load)")
    parser.add_argument("--slow", action="store_true", help="also run the days aoc_answers.rs marks slow")
    parser.add_argument("--against", type=Path, help="an earlier result JSON to compare with (default: the previous run)")
    parser.add_argument("--no-diff", action="store_true", help="don't compare with any earlier run")
    opts = parser.parse_args()

    answers, slow = read_answers(ANSWERS_RS.read_text())
    days = sorted(d for d in answers if opts.slow or d not in slow)
    days = [d for d in select(days, opts.filter) if (ROOT / "aoc" / "inputs" / d[0] / f"day{d[1]}.txt").exists()]
    if not days:
        sys.exit("no day matches the filter")
    if compare.instructions_wrapper(platform.system()) is None:
        print("warning: no way to count instructions here; wall time only", file=sys.stderr)

    with ThreadPoolExecutor(max_workers=max(1, opts.jobs)) as pool:
        def one(day):
            record = measure(opts.sw, day, answers[day], opts.timeout)
            print(f"{label(day)}: {record['status']}, {fmt_count(record['instructions'])} instructions", file=sys.stderr, flush=True)
            return label(day), record
        results = dict(pool.map(one, days))

    OUT.mkdir(parents=True, exist_ok=True)
    stamp = datetime.datetime.now().strftime("%Y-%m-%dT%H%M%S")
    path = OUT / f"{stamp}-{platform.node().split('.')[0]}.json"
    meta = {"filter": opts.filter, "timeout": opts.timeout, "jobs": opts.jobs, "date": stamp, "host": platform.node(), "system": platform.system()}
    path.write_text(json.dumps({"meta": meta, "days": results}, indent=1))

    print(table(results))
    bad = sorted(n for n, r in results.items() if r["status"] != "ok")
    if bad:
        print("\nnot ok: " + ", ".join(f"{n} ({results[n]['status']})" for n in bad))
    old_path = None if opts.no_diff else (opts.against or previous_run(path))
    if old_path:
        rows, mean = diff(results, json.loads(old_path.read_text())["days"])
        print("\n" + diff_table(rows, mean, old_path.name))
    print(f"\nwrote {path.relative_to(ROOT)}")
    # Wrong answers and failures matter; timeouts are only reported.
    sys.exit(1 if any(r["status"] in ("wrong", "build-fail", "run-fail") for r in results.values()) else 0)


if __name__ == "__main__":
    main()
