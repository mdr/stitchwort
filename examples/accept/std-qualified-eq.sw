-- `Std.Eq.flipped` works without any import; so does dot notation.
theorem flip ∀ (a b: Nat) (p: a = b): b = a := Std.Eq.flipped p

theorem flipDot ∀ (a b: Nat) (p: a = b): b = a := p.flipped
