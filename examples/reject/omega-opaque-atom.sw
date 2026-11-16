-- expect-error: E-ARITHMETIC
-- A product of two unknowns is not linear, so `arithmetic` treats `x * y` as an atom.
import Std (Nat)

theorem atomic (x: Nat) (y: Nat): x ≤ x * y := arithmetic
