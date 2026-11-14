def countBig: List Nat → Nat
  | [] => 0
  | [x, ..rest] if x > 3 => 1 + countBig rest
  | [_, ..rest] => countBig rest

theorem countBigAtMost ∀ (xs: List Nat): countBig xs ≤ xs.length := match induct (countBig xs) with
  | eq1 => omega
  | eq2 x rest big ih => ?
  | eq3 x rest small ih => omega
