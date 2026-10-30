-- Accepted neighbours of the must-reject examples for kernel bugs other
-- proof assistants had in 2026 (docs/research/kernel.md §5.4, ticket T1).

def f: Nat → Nat
  | Zero => 0
  | Succ _ => 1

def g: Nat → Nat
  | Zero => 0
  | Succ _ => 1

-- soundness/conversion-memo-*.sw: two definitions with the same case tree
-- are equal on equal arguments, each pair compared.
theorem good (x y: Nat): (f x, f y) = (g x, g y) := rfl

-- soundness/j-on-hypothesis-stuck.sw and identity-is-not-constant.sw: `J`
-- computes on `rfl`.
theorem kOnRfl: J (z _ => Nat) 5 (rfl: 0 = 0) = 5 := rfl

-- soundness/record-of-proof-not-convertible.sw: a value of `Box` is equal
-- to itself.
type Box = { h: 0 = 0 }

theorem box (p: Box): p = p := rfl
