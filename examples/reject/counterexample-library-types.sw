-- expect-error: E-REFL
-- Inputs of the library's types: a `Float` (random ones include the NaN),
-- `Fin` and `Vec` of a known size, and maps and sets, built with
-- `Map.fromList` so they keep their invariant (counterexample search
-- stage 2).
import Std (Float, Fin, Vec, Map, Set)

theorem equalsItself (x: Float): Float.ieeeEq x x = True := rfl

theorem belowFour (i: Fin 5): Fin.toNat i < 4 := rfl

theorem headIsZero (v: Vec Nat 3): Vec.head v = 0 := rfl

theorem mapEmpty (m: Map Nat Nat): Map.size m = 0 := rfl

theorem setEmpty (s: Set Nat): Set.size s = 0 := rfl
