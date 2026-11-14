-- Division is total, with Lean's values: `x / 0 = 0` and `x % 0 = x`, on
-- `Nat` and in every `Int` convention, so `x = (x / d) * d + x % d` holds for
-- every `d`. A divisor needs no proof that it isn't 0.
import Std (Int, Nat)

def ratio (n d: Nat): Nat := n / d

test "Nat by 0" := 7 / 0 == 0 ∧ 7 % 0 == 7 ∧ 0 / 0 == 0 ∧ 0 % 0 == 0
test "a variable divisor" := ratio 7 2 == 3 ∧ ratio 7 0 == 0
test "Nat.divMod and Nat.ceilDiv by 0" := Nat.divMod 7 0 == MkPair 0 7 ∧ Nat.ceilDiv 7 0 == 0

test "Int by 0" := (-7: Int) / 0 == 0 ∧ (-7: Int) % 0 == -7 ∧ (7: Int) % 0 == 7
test "every Int convention by 0" :=
  Int.tdiv (-7) 0 == 0 ∧ Int.tmod (-7) 0 == -7 ∧ Int.fdiv (-7) 0 == 0 ∧ Int.fmod (-7) 0 == -7
test "Int.modNat by 0" := Int.modNat 7 0 == 7 ∧ Int.modNat (-7) 0 == 0

theorem divByZero ∀ (n: Nat): n / 0 = 0 := Nat.divZero n

theorem modByZero ∀ (n: Nat): n % 0 = n := Nat.modZero n

theorem divisionLaw ∀ (n d: Nat): n = (n / d) * d + n % d := Nat.divModEq n d

theorem intDivisionLaw ∀ (a d: Int): d * (a / d) + a % d = a := Int.divAddMod a d
