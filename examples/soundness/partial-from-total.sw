-- expect-error: E-PARTIAL
-- The guarantee `Partial` exists for (docs/proposals/partial.md §3): a
-- function whose type doesn't say `Partial` finishes, everything it calls
-- included. So a total function can't call a partial one, as Lean's
-- `partial def` would allow (its partiality is invisible in types).
collatzSteps : Nat -> {Partial} Nat
collatzSteps 1 = 0
collatzSteps n = 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

innocent : Nat -> Nat
innocent n = collatzSteps n + 1
