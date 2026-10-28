-- Adding bit by bit: each bit of `x + y` is the exclusive or of the bits of
-- `x` and `y` and the carry into it, and each carry comes from the bits and
-- the carry below, as a ripple-carry adder computes them.

namespace Aoc.Year2024.Day24.Proofs
import Std (Bool, Eq, Nat, Void)

-- The carry out of adding bits `a` and `b` with `carry` in: both bits set,
-- or exactly one with a carry in.
def carryOut (a: Bool) (b: Bool) (carry: Bool): Bool := (a ∧ b) ∨ (Bool.xor a b ∧ carry)

-- The carry into bit `bit` when adding `x` and `y` with `carry` into bit 0.
def carryFrom (x: Nat) (y: Nat) (carry: Bool): Nat → Bool
  | Zero => carry
  | Succ bit => carryOut (Nat.testBit x bit) (Nat.testBit y bit) (carryFrom x y carry bit)

-- The carry into bit `bit` when adding `x` and `y`.
def carryInto (x: Nat) (y: Nat) (bit: Nat): Bool := carryFrom x y False bit

theorem testBitZero (n: Nat): Nat.testBit n 0 = (n % 2 == 1) := rewrite Nat.shiftRightNone n in rfl

theorem toNatOdd: (carry: Bool) → (carry.toNat % 2 == 1) = carry
  | False => rfl
  | True => rfl

-- The lowest bit of a sum of two numbers and a carry.
theorem lowSumBit (x: Nat) (y: Nat) (carry: Bool):
    Nat.testBit (x + y + carry.toNat) 0 = Bool.xor (Bool.xor (Nat.testBit x 0) (Nat.testBit y 0)) carry :=
  rewrite testBitZero (x + y + carry.toNat), testBitZero x, testBitZero y, Nat.oddSum (x + y) carry.toNat, Nat.oddSum x y, toNatOdd carry in rfl

-- Half the sum of two bits and a carry is the carry out.
theorem halfBits: (a: Nat) → (b: Nat) → (carry: Bool) → a < 2 → b < 2 → (a + b + carry.toNat) / 2 = (carryOut (a == 1) (b == 1) carry).toNat
  | Zero, Zero, False, small, alsoSmall => rfl
  | Zero, Zero, True, small, alsoSmall => rfl
  | Zero, Succ Zero, False, small, alsoSmall => rfl
  | Zero, Succ Zero, True, small, alsoSmall => rfl
  | Succ Zero, Zero, False, small, alsoSmall => rfl
  | Succ Zero, Zero, True, small, alsoSmall => rfl
  | Succ Zero, Succ Zero, False, small, alsoSmall => rfl
  | Succ Zero, Succ Zero, True, small, alsoSmall => rfl
  | Succ (Succ a), b, carry, small, alsoSmall => Void.exfalso (omega)
  | a, Succ (Succ b), carry, small, alsoSmall => Void.exfalso (omega)

-- Halving a sum of two numbers and a carry: the halves, and the carry out
-- of the lowest bits.
theorem halfSum (x: Nat) (y: Nat) (carry: Bool):
    (x + y + carry.toNat) / 2 = x / 2 + y / 2 + (carryOut (Nat.testBit x 0) (Nat.testBit y 0) carry).toNat :=
  rewrite testBitZero x, testBitZero y in
    omega [halfBits (x % 2) (y % 2) carry (Nat.modLess x 2 (Nat.succNotZero 1)) (Nat.modLess y 2 (Nat.succNotZero 1))]

-- The carry into bit `bit + 1` is the carry into bit `bit` of the halves,
-- with the carry out of the lowest bits.
theorem carryFromHalves (x: Nat) (y: Nat) (carry: Bool): (bit: Nat) →
    carryFrom x y carry (Succ bit) = carryFrom (x / 2) (y / 2) (carryOut (Nat.testBit x 0) (Nat.testBit y 0) carry) bit
  | Zero => rfl
  | Succ bit =>
    rewrite carryFromHalves x y carry bit, Nat.testBitSucc x bit, Nat.testBitSucc y bit in rfl

-- Each bit of a sum of two numbers and a carry.
theorem sumBitFrom: (bit: Nat) → (x: Nat) → (y: Nat) → (carry: Bool) →
    Nat.testBit (x + y + carry.toNat) bit = Bool.xor (Bool.xor (Nat.testBit x bit) (Nat.testBit y bit)) (carryFrom x y carry bit)
  | Zero, x, y, carry => lowSumBit x y carry
  | Succ bit, x, y, carry =>
    rewrite Nat.testBitSucc (x + y + carry.toNat) bit, halfSum x y carry, Nat.testBitSucc x bit, Nat.testBitSucc y bit,
      carryFromHalves x y carry bit in
      sumBitFrom bit (x / 2) (y / 2) (carryOut (Nat.testBit x 0) (Nat.testBit y 0) carry)

-- Each bit of `x + y`: the bits of `x` and `y` and the carry into it.
theorem sumBit (x: Nat) (y: Nat) (bit: Nat): Nat.testBit (x + y) bit = Bool.xor (Bool.xor (Nat.testBit x bit) (Nat.testBit y bit)) (carryInto x y bit) :=
  rewrite Eq.sym (Nat.addZero (x + y)) in sumBitFrom bit x y False
