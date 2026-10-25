-- expect-error: E-JS-PARTIAL
-- Generated JavaScript can't run a partial computation, so an export whose
-- type mentions `Partial` is refused (docs/proposals/partial.md §7.6).
def collatzSteps: Nat → {Partial} Nat
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

export def steps (n: Nat): {Partial} Nat := collatzSteps n
