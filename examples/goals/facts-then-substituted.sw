-- `then ?` gets each part as written, `f b = 2 ∨ f a = 1`, though the
-- other parts were closed by substituting with `e`.

theorem thenSubst ∀ (f: Nat → Nat) (a b: Nat)
    (e: a = b)
    (k: f a = 1):
    f b = 1 ∧ f a + 1 = f a + 1 ∧ (f b = 2 ∨ f a = 1) :=
  byFacts then ?
