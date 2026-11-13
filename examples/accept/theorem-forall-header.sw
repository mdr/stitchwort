-- A theorem's header may say `∀` before its parameters (D3472): only
-- spelling, so the theorems below are the same as without it.
theorem plusZero ∀ (n: Nat): n + 0 = n := rfl

theorem sameValue forall [a: Type] (x: a): x = x := rfl

-- Implicit parameters alone need none.
theorem implicitOnly [n: Nat]: n + 0 = n := rfl
