-- Pairs with reject/wrong-proof.sw: a true statement is proved by computation.
theorem fourIsFour : 2 + 2 = 4
fourIsFour = rfl

-- `0 + n = n` holds by computation, because `+` recurses on its first argument.
theorem zeroPlus : (n : Nat) -> 0 + n = n
zeroPlus n = rfl
