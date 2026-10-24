-- expect-error: E-REWRITE-NOTHING

import Std (Nat)

-- `rewrite` compares what terms compute to: `n / 1` computes to
-- `Nat.divFuel n n 1` and `Succ n / 1` to `Succ (Nat.divFuel n n 1)`, so the
-- first rule replaces both, and the second finds nothing left to replace.
-- The message shows what it looked for and that the goal already holds.
theorem bad (n: Nat): n / 1 + Succ n / 1 = n + Succ n :=
  rewrite Nat.divOne n, Nat.divOne (Succ n)
