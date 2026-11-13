-- Every recursive function comes with an induction principle that follows
-- its own shape: one case for each of its equations, with the hypothesis for
-- each recursive call. `match induct (f args)` uses it, so the proof is
-- about the branches the function really has, not about the type's cases.
def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if k ≤ x then Succ (countAbove k xs) else countAbove k xs

theorem countAboveLe ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ xs.length := match induct (countAbove k xs) with
  | eq1 => omega
  | eq2IfTrue y ys h ih => omega
  | eq2IfFalse y ys h ih => omega

-- The equations are theorems too. `countAbove.eq2.ifFalse` says what a call
-- is when the test failed, with the failed test as a hypothesis.
theorem skipsSmall ∀ (k: Nat) (x: Nat) (xs: List Nat) (h: (k <= x) = False):
    countAbove k [x, ..xs] = countAbove k xs :=
  countAbove.eq2.ifFalse k x xs h
