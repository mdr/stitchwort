# AoC 2025 day 1 in Lean 4, Agda and Idris 2

These are ports of `aoc/day01.sw` (Stitchwort), written to compare how hard the proofs
are. The write-up is in `docs/comparisons/aoc-day01.md`. Each file states the same
theorem, `zerosPassedCorrect`: the arithmetic count of part 2 equals the
click-by-click count, for any dial size, start and list of turns. Each file also has
`part2Puzzle` and the puzzle example (part 1 = 3, part 2 = 6).

Nothing is installed globally. Each prover comes from nixpkgs through `nix shell`.
The repository's flake doesn't check these files.

## Lean 4 (core only, no Mathlib)

```
cd comparisons/aoc-day01/lean
nix shell nixpkgs#lean4 -c lean Day01.lean
```

Expected output: `(3, 6)` from the `#eval`, and no errors. The two `example`s check the
puzzle example in the kernel (`decide +kernel`).

## Agda (standard library 2.3)

```
cd comparisons/aoc-day01/agda
nix shell --impure --expr 'with import <nixpkgs> {}; agda.withPackages (p: [ p.standard-library ])' \
  -c agda --safe Day01.agda
```

Expected output: `Checking Day01 (…)` and nothing else. `day01.agda-lib` makes the file
depend on `standard-library`. The puzzle example is checked by `refl` while the file is
type-checked.

## Idris 2 (base + contrib)

```
cd comparisons/aoc-day01/idris
nix shell nixpkgs#idris2 -c idris2 -p contrib --check Day01.idr             # check
nix shell nixpkgs#idris2 -c idris2 -p contrib Day01.idr -o day01 && ./build/exec/day01
```

Checking prints `1/2: Building DialArith …` and `2/2: Building Day01 …`, plus deprecation
warnings from contrib. Running prints `(3, (6, 6))`: part 1, part 2, and the
click-by-click specification. `DialArith.idr` holds `mod`/`div` by the dial's size
behind `export`, so the type checker can't unfold them (see the write-up). One cost of
that: the example can only be checked by running the program, not by `Refl`.
