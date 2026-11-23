-- expect-error: E-REFL
-- A local definition (`addTwo.helper`) can't be named in an `unfolding`
-- clause: the note suggests unfolding its owner, which unfolds it.
import Std (Nat)

opaque def two: Nat := 2

opaque def addTwo (n: Nat): Nat unfolding two :=
  def helper (m: Nat): Nat := two + m
  helper n

theorem addTwoOne: addTwo.helper 1 = 3 := byComputing
