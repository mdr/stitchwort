-- An `_` in a fact given to `omega` that nothing else pins down is worked out
-- from the goal: the fact's atom `tally _ xs` is the goal's `tally 3 xs`.

import Std (Nat, List)

def tally (label: Nat): List Nat → Nat
  | [] => 0
  | Cons head rest => 1 + tally label rest

def size: List Nat → Nat
  | [] => 0
  | Cons head rest => 1 + size rest

theorem tallyAtMostSize (label: Nat): (xs: List Nat) → tally label xs ≤ size xs
  | [] => omega
  | Cons head rest => omega [tallyAtMostSize label rest]

theorem listed (xs: List Nat): tally 3 xs ≤ size xs + 1 :=
  omega [tallyAtMostSize _ xs]

theorem viaLet (xs: List Nat) (extra: Nat): tally 3 xs ≤ size xs + extra :=
  let bound := tallyAtMostSize _ xs
  omega [bound]

-- The unknown sits inside an argument: `1 + _` is the goal's `4`.
theorem inside (xs: List Nat): tally 4 xs ≤ size xs + 1 :=
  omega [tallyAtMostSize (1 + _) xs]
