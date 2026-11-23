-- expect-error: E-REFL
-- Two stuck casts are compared by their ends, motive and base, never by
-- their proofs (docs/proposals/full-proof-irrelevance-audit.md, finding B):
-- along `x = y` and along `x = z`, their ends differ, so they do. Partner:
-- `sameEnds` in accept/rules-k-and-s.sw.
import Std (Nat, Eq)

def castAt (x y: Nat) (h: x = y) (d: Nat): Nat := J (w e => Nat) d h

theorem differentEnds ∀ (x y z: Nat) (h1: x = y) (h2: x = z): castAt x y h1 3 = castAt x z h2 3 := byComputing
