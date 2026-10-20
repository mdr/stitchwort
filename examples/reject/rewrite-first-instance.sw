-- expect-error: E-REFL
-- The first match, `f 1`, fixes the rule's `n` to 1. `f 2` is a different
-- instance and stays, so `rfl` is left with `g 1 + f 2 = g 1 + g 2`.
theorem bad (f: Nat -> Nat) (g: Nat -> Nat) (h: [n: Nat] -> f n = g n): f 1 + f 2 = g 1 + g 2 :=
  rewrite h
