-- expect-error: E-REFL
-- A statement false only for lists of 12 elements or more: too long for the
-- small inputs tried first, so a random list finds it, and shrinking makes
-- it a smallest one, twelve zeros (counterexample search stage 2).
import Std (List)

def chunks (xs: List Nat): Nat := if List.length xs < 12 then 1 else 2

theorem oneChunk (xs: List Nat): chunks xs = 1 := rfl
