# spectral-norm

The Benchmarks Game's program: the largest singular value of the infinite
matrix `a(i, j) = 1 / ((i + j)(i + j + 1) / 2 + i + 1)`, cut to N by N
(N = 1000 here), by ten rounds of the power method on `AᵀA`. The answer is
printed to nine decimals.

Differences from the game's programs, none in the arithmetic of the loops:

- **Square root.** Stitchwort has no `Float.sqrt` yet (SW-2458), so its one
  final root is Newton's method (30 steps from 1.0). CPython and Lean call
  their `sqrt`. Both agree far beyond nine digits; the cost is one call.
- **Printing.** Python prints with `%0.9f`. Stitchwort and Lean scale by 10^9,
  round, and insert the point, since neither has a fixed-decimal formatter.
  They differ from `%0.9f` only on an exact tie.
- **Structure.** `A·v` and `Aᵀ·v` are one function with a flag, each entry
  recomputed on the fly (the game's programs do the same); results are
  arrays of `Float` (Python lists) built per call, not updated in place.
- **Summing.** Each row is a left fold from `0.0`. CPython 3.12+'s `sum`
  compensates its float sums, so its last bits may differ; nothing shows in
  nine digits.
