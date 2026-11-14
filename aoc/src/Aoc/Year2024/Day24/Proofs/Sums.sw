--| Adding bit by bit: each bit of `x + y` is the exclusive or of the bits of
--| `x` and `y` and the carry into it, and each carry comes from the bits and
--| the carry below, as a ripple-carry adder computes them.

namespace Aoc.Year2024.Day24.Proofs
import Std (Bool, Eq, Nat, Void)

--| The carry out of adding bits `a` and `b` with `carry` in: both bits set,
--| or exactly one with a carry in.
def carryOut (a b carry: Bool): Bool := (a ∧ b) ∨ (Bool.xor a b ∧ carry)

--| The carry into bit `bit` when adding `x` and `y` with `carry` into bit 0.
def carryFrom (x y: Nat) (carry: Bool): Nat → Bool
  | Zero => carry
  | Succ bit => carryOut (Nat.testBit x bit) (Nat.testBit y bit) (carryFrom x y carry bit)

--| The carry into bit `bit` when adding `x` and `y`.
def carryInto (x y bit: Nat): Bool := carryFrom x y False bit

theorem testBitZero ∀ (n: Nat): n.testBit 0 = (n % 2 == 1) := rewrite Nat.shiftRightNone n in rfl

--| The lowest bit of a sum of two numbers and a carry.
theorem lowSumBit ∀ (x y: Nat) (carry: Bool):
    Nat.testBit (x + y + carry.toNat) 0 = ((x.testBit 0).xor (y.testBit 0)).xor carry :=
  rewrite testBitZero (x + y + carry.toNat),
      testBitZero x,
      testBitZero y,
      Nat.oddSum (x + y) carry.toNat,
      Nat.oddSum x y,
      Bool.toNatOdd carry in
    rfl

--| Half the sum of two bits and a carry is the carry out.
theorem halfBits ∀ (a b: Nat) (carry: Bool)
    (small: a < 2)
    (alsoSmall: b < 2):
    (a + b + carry.toNat) / 2 = (carryOut (a == 1) (b == 1) carry).toNat :=
  match a, b, carry with
    | Zero, Zero, False => rfl
    | Zero, Zero, True => rfl
    | Zero, Succ Zero, False => rfl
    | Zero, Succ Zero, True => rfl
    | Succ Zero, Zero, False => rfl
    | Succ Zero, Zero, True => rfl
    | Succ Zero, Succ Zero, False => rfl
    | Succ Zero, Succ Zero, True => rfl

--| Halving a sum of two numbers and a carry: the halves, and the carry out
--| of the lowest bits.
theorem halfSum ∀ (x y: Nat) (carry: Bool):
    (x + y + carry.toNat) / 2 = x / 2 + y / 2 + (carryOut (x.testBit 0) (y.testBit 0) carry).toNat :=
  rewrite testBitZero x, testBitZero y in
    omega [halfBits (x % 2) (y % 2) carry (Nat.modLess x 2 (Nat.succNotZero 1)) (Nat.modLess y 2 (Nat.succNotZero 1))]

--| The carry into bit `bit + 1` is the carry into bit `bit` of the halves,
--| with the carry out of the lowest bits.
theorem carryFromHalves ∀ (x y: Nat) (carry: Bool) (bit: Nat):
    carryFrom x y carry (Succ bit) = carryFrom (x / 2) (y / 2) (carryOut (x.testBit 0) (y.testBit 0) carry) bit :=
  match bit with
    | Zero => rfl
    | Succ bit => rewrite carryFromHalves x y carry bit, Nat.testBitSucc x bit, Nat.testBitSucc y bit in rfl

--| Each bit of a sum of two numbers and a carry.
theorem sumBitFrom ∀ (bit x y: Nat) (carry: Bool):
    Nat.testBit (x + y + carry.toNat) bit = ((x.testBit bit).xor (y.testBit bit)).xor (carryFrom x y carry bit) :=
  match bit with
    | Zero => lowSumBit x y carry
    | Succ bit =>
      rewrite Nat.testBitSucc (x + y + carry.toNat) bit,
          halfSum x y carry,
          Nat.testBitSucc x bit,
          Nat.testBitSucc y bit,
          carryFromHalves x y carry bit in
        sumBitFrom bit (x / 2) (y / 2) (carryOut (Nat.testBit x 0) (Nat.testBit y 0) carry)

--| Each bit of `x + y`: the bits of `x` and `y` and the carry into it.
theorem sumBit ∀ (x y bit: Nat):
    Nat.testBit (x + y) bit = ((x.testBit bit).xor (y.testBit bit)).xor (carryInto x y bit) :=
  rewrite Eq.sym (Nat.addZero (x + y)) in sumBitFrom bit x y False
