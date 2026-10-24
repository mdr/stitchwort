-- expect-error: E-REFL
-- A true statement with a broken proof: the search finds no counterexample,
-- and says nothing (acceptance test 3).
theorem addComm (a: Nat) (b: Nat): a + b = b + a := rfl
