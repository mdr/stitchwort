-- Bitwise AND, OR and shifting left on `Nat`, with the lemmas that say what
-- each bit of the result is.

import Std (Nat)

def mask (value: Nat) (bits: Nat): Nat := Nat.and value (Nat.shiftLeft 1 bits - 1)

def setBit (value: Nat) (bit: Nat): Nat := Nat.or value (Nat.shiftLeft 1 bit)

theorem maskBit (value: Nat) (other: Nat) (i: Nat): Nat.testBit (Nat.and value other) i = (Nat.testBit value i ∧ Nat.testBit other i) :=
  Nat.testBitAnd i value other

theorem setKeeps (value: Nat) (bit: Nat) (i: Nat) (set: Nat.testBit value i = True): Nat.testBit (setBit value bit) i = True :=
  rewrite Nat.testBitOr i value (Nat.shiftLeft 1 bit), set in rfl

theorem shiftBack (value: Nat) (count: Nat): Nat.shiftRight (Nat.shiftLeft value count) count = value := Nat.shiftRightShiftLeft value count

test "mask" := mask 182 4 == 6

test "setBit" := setBit 8 1 == 10

test "shiftLeft" := Nat.shiftLeft 5 3 == 40
