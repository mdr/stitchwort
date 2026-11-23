-- A body with an `unfolding` clause unfolds its own local definitions and
-- lifted `match`es, which the clause makes opaque: they are part of the
-- body (docs/core.md, "Opaque definitions"). So `helper n` computes in
-- `first`, and in `twoAgain` the `match` proving `same` sees `pick`'s.
import Std (Nat, Eq, Bool)

opaque def two: Nat := 2

theorem twoPlus ∀ (n: Nat) (b: Bool): (two + n = 2 + n) ∧ (b = b) unfolding two :=
  def helper (m: Nat): Nat := two + m
  let first: helper n = 2 + n := byComputing
  let second: b = b := match b with
    | True => byComputing
    | False => byComputing
  (first, second)

theorem twoAgain ∀ (b: Bool): (if b then two else 2) = 2 unfolding two :=
  let pick: Nat := match b with
    | True => two
    | False => 2
  let same: pick = 2 := match b with
    | True => byComputing
    | False => byComputing
  match b with
    | True => byComputing
    | False => byComputing

opaque def addTwo (n: Nat): Nat unfolding two :=
  def helper (m: Nat): Nat := two + m
  helper n

-- Unfolding the owner unfolds its local definitions too.
theorem addTwoOne: addTwo.helper 1 = 3 unfolding addTwo := byComputing
