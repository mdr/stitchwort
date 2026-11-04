-- expect-error: E-TAILREC
-- The recursion of a definition by `decreasing` is checked as written.
import Std (Nat)

@[tailrec]
def half (n: Nat): Nat decreasing n :=
  if h: n < 2 then 0 else half (n - 2) + 1
