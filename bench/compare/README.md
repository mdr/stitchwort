# Stitchwort against CPython, PyPy and Lean

The harness for the plan in
[docs/proposals/comparative-speed.md](../../docs/proposals/comparative-speed.md)
(epic Comparative speed). It runs each program in each language, checks that
every one prints the same answer, and times them. It is a manual measurement
on a quiet machine, not a test.

## Running it

```
task bench:compare:check                     # every runner once, answers only
task bench:compare                           # check, then time with hyperfine
task bench:compare -- --runs 3 pidigits      # options and program names after --
task bench:compare -- --all                  # also `run --js` and `run --native` (the JIT)
task bench:compare -- --runners native,cpython,pypy,lean   # only these runners (a slow machine skips `run`, `lean-run`)
```

Both tasks build `stitchwort` and its native runtime library, then run
`compare.sh` in `nix develop .#compare` (the default shell plus Lean 4,
hyperfine and PyPy). Output goes to `target/compare/<date>-<host>.json` and
`.md`.

The runners, named as in the table:

| Runner | Command |
|---|---|
| `run` | `stitchwort run` (the bytecode machine) |
| `native` | the executable from `stitchwort build --native` |
| `js`, `jit` | `run --js`, `run --native` (only with `--all`) |
| `cpython`, `pypy` | `python3`, `pypy3` on `<name>/main.py` |
| `lean` | the `lake build` executable |
| `lean-run` | `lean --run` on the Lean file |

The headline pairs (D3340) are `native` against `cpython` and `lean`; `run`
against `cpython` is reported too. No targets (D3341). Each language uses its
own natural data structures (D3342): Python's `dict` is not hobbled to match
our persistent `Map`.

## How it works

1. Build: `lake build` for the Lean programs, `stitchwort build --native` for
   each Stitchwort entry. Build times are reported apart, never in run times.
2. Check: each runner is run once on the program's input and its standard
   output compared byte for byte with `<name>/expected.txt`. A runner that
   disagrees, fails or doesn't build is marked FAIL and is **not timed**. A
   runner with no port or tool is SKIP. The check task exits 1 on any FAIL.
3. Time: `hyperfine --warmup 1 --runs N` per runner (3 runs for anything whose
   check run took over 30 s). The `null` program, which prints `ok`, is timed
   the same way; its median is the runner's startup and is subtracted from
   every row. A spread (max - min) over 5% of the median gets a `*`: rerun it.

Startup of `run` and `native` is measured on `null/main.sw`, a file, while the
AoC programs run as functions of the `aoc/` project, which loads the project
first. The AoC rows' startup is therefore a little more than the null row's.

## Adding a program

1. A folder `bench/compare/<name>/` with `expected.txt` (the answer, byte for
   byte; for a generated input, all languages must agree before it is
   committed) and `main.py` (Python, natural structures, same algorithm).
2. An entry in `programs.toml`: `stitchwort` (an `aoc/` function such as
   `Aoc.Year2020.Day15.main`, or a `.sw` file), and `input` / `args` if any.
   An AoC day is run from `aoc/` as it is; if it needs a size, give it an
   `IO.args()` entry as 2020 day 15 has.
3. Optionally the Lean port, `lean/Compare/<CamelCaseName>.lean` with a
   `main`, and a `[[lean_exe]]` in `lean/lakefile.toml` named `<name>` with
   `-` as `_`.
4. `task bench:compare:check -- <name>`.

A program should take at least 0.3 s in its fastest language and at most about
60 s in its slowest.

## What is here

`null`, `pidigits` and `binary-trees` (the Benchmarks Game classics, at 10,000
digits and depth 18) and `memory-game` (2020 day 15, part 2 at 30,000,000
turns) have all four languages. `dijkstra`, `octopus`, `disk`, `expressions`,
`scan`, `matcher` and `bridge` (AoC days) have Stitchwort, Python and Lean.

Most of the AoC days run a scaled copy of the real input so that Lean takes
0.4 to 0.6 s, not the 20 to 60 ms of the real one. `programs.toml` gives each a
`source`, a `repeat` and a `scale`; the harness writes the copy to
`target/compare/inputs/` on every run and hands it to every runner, so nothing
scaled is committed. `expressions` repeats the real input 180 times, `scan`
200 and `bridge` 150; `matcher` keeps the rules once and repeats the messages
16 times; `disk` repeats the disk map 45 times with a `0` between copies, so
files and gaps still alternate. `octopus` is the real grid tiled 2 by 2, where
Lean takes about 0.14 s, below the 0.3 s floor: a bigger cavern rarely flashes
all at once, and the one that does (30 by 30) takes `run` over two minutes.
After changing a scale, regenerate `expected.txt` from the Lean program and
check that the other runners agree.
