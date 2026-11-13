def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if k ≤ x then Succ (countAbove k xs) else countAbove k xs

theorem countAboveLe (k: Nat) (xs: List Nat): countAbove k xs ≤ xs.length := match induct (countAbove k xs) with
  | eq1 => omega
  | eq2IfTrue y ys h ih => ?
  | eq2IfFalse y ys h ih => omega
