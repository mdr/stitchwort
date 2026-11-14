# bench/aoc: native speed of every AoC day

`task bench:aoc` builds each Advent of Code day's `main` natively
(`stitchwort build --native`), runs it on its committed input, and records
instructions retired and wall time. It answers "did a speed change move any
day outside the ten `bench/compare` programs?". A measurement, not a test.

```
task bench:aoc                         # all days except the slow ones
task bench:aoc FILTER=2024             # a year
task bench:aoc FILTER='2024/0[1-3]'    # a regex searched in "YEAR/DAY"
task bench:aoc -- --against OLD.json   # compare with a chosen earlier run
task bench:aoc -- --slow --timeout 120 # also the days aoc_answers.rs marks slow
```

- Builds like `bench:compare`: `stitchwort` and its runtime are built
  non-incrementally into `target/bench` (SW-2474), so counts are comparable
  across checkouts.
- Answers are checked against `crates/cli/tests/running/aoc_answers.rs`,
  which `sweep.py` reads, so there is one list. A wrong answer, a build
  failure or a crash fails the run; a timeout (60 s, `--timeout`) is
  reported and its process group killed, but is not a failure.
- Instructions come from `/usr/bin/time -l` (macOS) or `perf stat` (Linux),
  through `bench/compare/compare.py`. Without either, only wall time is
  recorded.
- Results go to `target/bench-aoc/<time>-<host>.json`. After a run, the
  change per day against the previous file there is printed (days over 3%
  are marked); `--no-diff` skips it. The previous file may have been made
  with a different FILTER; days not in both are left out.
- `-j N` runs days in parallel; wall time and counts then drift, so the
  default is 1.

`python3 -I bench/aoc/test_sweep.py` tests the answer reading and diffing.
