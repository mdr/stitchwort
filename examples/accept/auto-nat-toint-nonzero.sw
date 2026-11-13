-- `auto` proves `Nat.toInt d ≠ 0` from a hypothesis `d ≠ 0`, so a lemma about
-- an `Int` remainder can take a natural divisor written with `Nat.toInt`.

import Std (Int, Nat)

def modByNat (x: Int) (d: Nat): Int := x % Nat.toInt d

def divByNat (x: Int) (d: Nat): Int := x / Nat.toInt d

theorem modByNatNonneg ∀ (x: Int) (d: Nat) [auto ok: d ≠ 0]: 0 ≤ modByNat x d := Int.modNonneg x (Nat.toInt d)

test "remainder by a natural" := modByNat 17 5 == 2

test "division by a natural" := divByNat 17 5 == 3

test "a negative remainder" := modByNat (-18) 100 == 82
