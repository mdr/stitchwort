theorem t ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs := match induct (countAbove k xs) with
  | eq1 => arithmetic
  | eq2IfTrue x xs h ih => arithmetic
  | eq2IfFalse x xs h ih => (arithmetic)
