theorem t ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs := match induct (countAbove k xs) with
  | eq1 => omega
  | eq2IfTrue x xs h ih => omega
  | eq2IfFalse x xs h ih => (omega)
