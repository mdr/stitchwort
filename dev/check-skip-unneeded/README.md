# check-skip-unneeded (SW-1193)

- `measure.py BASE PROTO AOC_DIR [RUNS]`: the measurement behind
  `dev/measurements/check-skip-unneeded.md`. `PROTO` is a build of this
  branch (the prototype is switched on by `STITCHWORT_SKIP_UNNEEDED=1`);
  `BASE` is a build without it. The two have separate cache entries (the
  build fingerprint differs), so the script warms both.
- `results-2026-11-04.log`: its output (3 rounds per edit, machine load 30-80).
- `results-as-built-2026-11-04.log`: the same against the built change
  (SW-1193, D2301), base = `main` at 06bd6c0d (load 16 falling to 9).
