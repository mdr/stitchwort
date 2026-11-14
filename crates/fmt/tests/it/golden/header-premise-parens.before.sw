-- R: a header binder's whole type loses redundant parentheses.
theorem extGet (xs ys: List a) (h: (∀ (i: Nat) => List.get xs i = List.get ys i)): xs = ys := h

-- Not the binder's whole type, so the parentheses stay.
theorem betweenLo (lo: Nat) (hi: Nat) (x: Nat) (h: (lo ≤ x ≤ hi) = True): lo ≤ x := h

-- A tuple type needs its parentheses, so they stay.
theorem fstOf (pair: (Nat, Nat)): Nat := pair.fst
