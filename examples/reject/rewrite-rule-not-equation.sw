-- expect-error: E-REWRITE-RULE

import Std (List, Nat)

-- A rule is a proof of an equation. Arguments left off its end are filled
-- in, but `h n` proves `List.Mem n [n]` whatever `n` is: not an equation.
theorem bad (h: (n: Nat) -> List.Mem n [n]) (n: Nat): n + 0 = n :=
  rewrite h
