-- expect-error: E-REFL
-- A local definition of a theorem with an `unfolding` clause is opaque, and
-- nothing can unfold the theorem: the note says so rather than suggesting a
-- clause that can't be written.
import Std (Nat, Eq)

opaque def two: Nat := 2

theorem twoPlus ∀ (n: Nat): two + n = 2 + n unfolding two :=
  def helper (m: Nat): Nat := two + m
  let first: helper n = 2 + n := byComputing
  first

theorem helperOne: twoPlus.helper 1 = 3 := byComputing
