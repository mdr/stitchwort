-- expect-error: E-OMEGA
-- A product of two unknowns is not linear, so `omega` treats `x * y` as an atom.
import Std (Nat)

theorem opaque (x: Nat) (y: Nat): x ≤ x * y := omega
