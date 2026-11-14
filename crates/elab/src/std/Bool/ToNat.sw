--| Lemmas about `Bool.toNat`: what a count of 0 means, `toNat` of a conjunction
--| and its parity.
-- A file of its own, after List/Sort.sw, which defines `Nat.keepIf` that
-- `Bool.toNatAnd` states its result with.

--| A `Bool` whose `toNat` is 0 is `False`.
theorem Bool.toNatEqZero ∀ (b: Bool) (h: Bool.toNat b = 0): b = False := match b with
  | False => rfl
  | True => Void.exfalso (Nat.succNotZero 0 h)

--| `toNat` of a conjunction: the second `Bool`'s count, kept only when the
--| first holds.
theorem Bool.toNatAnd ∀ (a: Bool) [b: Bool]: Bool.toNat (a ∧ b) = b.toNat.keepIf a := match a with
  | True => rfl
  | False => rfl

--| The parity of a `Bool`'s `toNat` is the `Bool`.
theorem Bool.toNatOdd ∀ (b: Bool): (b.toNat % 2 == 1) = b := match b with
  | False => rfl
  | True => rfl

test "Bool.toNatAnd" :=
  Bool.toNat (True ∧ False) == Nat.keepIf (Bool.toNat False) True
    ∧ Bool.toNat (True ∧ True) == Nat.keepIf (Bool.toNat True) True
    ∧ Bool.toNat (False ∧ True) == Nat.keepIf (Bool.toNat True) False
test "Bool.toNatEqZero" := Bool.toNat False == 0 ∧ Bool.toNat True != 0
test "Bool.toNatOdd" := (Bool.toNat True % 2 == 1) == True ∧ (Bool.toNat False % 2 == 1) == False
