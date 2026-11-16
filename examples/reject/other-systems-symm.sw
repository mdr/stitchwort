-- expect-error: E-UNKNOWN-NAME
-- Lean's `Eq.symm` (and Stitchwort's old `Eq.sym`) is `h.flipped` (D3654).
import Std (Eq, Nat)

theorem back (a b: Nat) (h: a = b): b = a := Eq.symm h
