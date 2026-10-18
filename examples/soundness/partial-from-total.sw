-- expect-error: E-PARTIAL
-- The guarantee `Partial` exists for (docs/proposals/partial.md §3): a
-- function whose type doesn't say `Partial` finishes, everything it calls
-- included. So a total function can't call a partial one, as Lean's
-- `partial def` would allow (its partiality is invisible in types).
def collatzSteps : Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def innocent (n : Nat) : Nat := collatzSteps n + 1
