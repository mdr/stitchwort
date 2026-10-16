-- expect-error: E-JS-PARTIAL
-- Generated JavaScript can't run a partial computation, so an export whose
-- type mentions `Partial` is refused (docs/proposals/partial.md §7.6).
collatzSteps : Nat -> {Partial} Nat
collatzSteps 1 = 0
collatzSteps n = 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

export steps : Nat -> {Partial} Nat
steps n = collatzSteps n
