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
task bench:compare -- --instructions         # also instructions retired (second table, JSON "instructions")
task bench:compare -- --runners native,cpython,pypy,lean   # only these runners (a slow machine skips `run`, `lean-run`)
```

Both tasks build `stitchwort` and its native runtime library, then run
`compare.sh` in `nix develop .#compare` (the default shell plus Lean 4,
hyperfine and PyPy). Output goes to `target/compare/<YYYY-MM-DD>T<HHMMSS>-<host>.json` and
`.md`.

On Linux the `compare` shell also carries `perf` (nixpkgs' top-level `perf`,
the kernel's perf tool; its version need not match the running kernel for
`perf stat` of hardware counters). It needs `kernel.perf_event_paranoid` of
2 or lower to count one's own processes; 2 is the upstream kernel default and
NixOS doesn't set it, so it normally works. Check with
`cat /proc/sys/kernel/perf_event_paranoid` (3 or more, as some hardened
kernels set, makes the cells `n/a`; lower it with
`sudo sysctl kernel.perf_event_paranoid=2`). A virtual machine without
exposed performance counters also gives `n/a`.

`--instructions` adds a second table after timing: for each program and
runner one more run, apart from hyperfine, counts instructions retired
(macOS: `/usr/bin/time -l`; Linux: `perf stat -e instructions -x,`, needs
`perf` on PATH and a kernel that allows it, else the cell is `n/a`). The
null program's count is subtracted as startup is. Use it where wall time is
noisy (a loaded laptop); the count barely moves with load. It is not
comparable across CPUs or languages as a measure of time, only as a steady
proxy for one machine. Raw counts (startup not subtracted) are in the JSON
under `instructions`. Parsing is tested by
`python3 -I bench/compare/test_instructions.py`.

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

## Sets and geometric means

`programs.toml` gives each program a `set`: `core` (the default) is the
original ten, and `wide` is the programs added to catch over-fitting to them
(SW-2450, docs/reviews/SW-2450-benchmark-breadth.md). After the tables,
`compare.py` prints the geometric mean of native / CPython and native / Lean
three ways: over the core programs, over the wide ones, and over all. Each
cell says how many programs it covers (a skipped or failed runner leaves a
program out of that cell), so a run of one program gives a mean of one. With
`--instructions` the same three means are printed for the instruction
counts. The wide mean is separate from the core one and is never folded into
the core ten's line in `history.toml`; a run that times the wide set adds
`wide_*` keys beside the core ones (format in `history.toml`'s header).

## Adding a program

1. A folder `bench/compare/<name>/` with `expected.txt` (the answer, byte for
   byte; for a generated input, all languages must agree before it is
   committed) and `main.py` (Python, natural structures, same algorithm).
2. An entry in `programs.toml`: `set` (`wide` for anything beyond the
   original ten; default `core`), `stitchwort` (an `aoc/` function such as
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
turns) have all four languages. `spectral-norm` (the wide set's first program, a float benchmark at N = 1000;
see its README) has all four too. `dijkstra`, `octopus`, `disk`, `expressions`,
`scan`, `matcher` and `bridge` (AoC days) have Stitchwort, Python and Lean.
`const-fold`, `rbmap` and `rbmap-ck` (wide set; Lean's own const_fold, rbmap and
rbmap_checkpoint, see "Lean's programs" below) have all four.

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

Lean's compiler merges repeated identical pure calls, so a port must not make
the same call twice where the others build two separate values. `binary-trees`
passes a `salt` that differs between the two `Tree.make` calls, as Lean's own
benchmark does. The other ports' generated C (`lean/.lake/build/ir/Compare/*.c`)
was read for removed or hoisted work: only small closed constants (numerals,
an empty `Array`) are hoisted to start-up, and no function makes the same call
twice.

## Lean's programs (wide set)

`const-fold`, `rbmap` and `rbmap-ck` are `tests/compile_bench/const_fold.lean`,
`rbmap.lean` and `rbmap_checkpoint.lean` of the Lean 4 repository, from the
reference-counting paper's suite (SW-2455). The Lean files in
`lean/Compare/` are theirs, with these changes:

- `Rbmap.lean` and `RbmapCk.lean`: a comment line at the top, nothing
  else. (Lean 4.34's `Array.mkArray` rename does not touch them.)
- `ConstFold.lean`: `main` also takes a second argument, a number of rounds
  (`round` builds the tree whose leaf values start at the round's number, so
  no round repeats another's work for the compiler to merge), and `unsafe` is
  dropped from `main`. Lean's `LEAN_STACK_SIZE_KB=4194304` is not set: at
  depth 20 the default stack is enough.

Sizes differ from Lean's benchmark sizes:

| Program | Lean's size | Here | Why |
|---|---|---|---|
| `const-fold` | depth 23, one round | depth 20, five rounds | native code stops at 2M frames of recursion (reassociating makes a chain of 2^depth additions); five rounds bring it to seconds |
| `rbmap` | 2,000,000 inserts | the same | |
| `rbmap-ck` | 2,000,000, every version kept | 400,000, every version kept | Stitchwort's tree nodes take about 160 bytes each, so 1,000,000 kept versions need over 4 GB |

The Stitchwort and Python ports write the tree out as Lean's does (a `Tree`
type, `balance1`/`balance2` as `balanceLeft`/`balanceRight` with the same
cases in the same order); neither uses `Map` or `dict`. Python's tree is
nested tuples, with a deep-recursion thread stack in `const-fold` only.
`rbmap-ck/main.sw` repeats `rbmap/main.sw`'s tree, as Lean's two files do.
