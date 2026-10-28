-- Bit facts the step's proof uses: XOR keeps the low bits of its sides, so
-- pruning can come before the XOR, and the XOR of two numbers below a power
-- of 2 is below it.

namespace Aoc.Year2024.Day22.Proofs
import Std (Eq, Nat)

-- The remainder by `2 ^ (k + 1)`: the remainder of half by `2 ^ k`, doubled,
-- and the lowest bit.
theorem modPowSucc (n: Nat) (k: Nat): n % Nat.pow 2 (Succ k) = n / 2 % Nat.pow 2 k * 2 + n % 2 :=
  let power := Nat.pow 2 k
  let positive := Nat.nonzeroOfPos power (Nat.powSuccPos 1 k)
  Nat.modUnique n (Nat.pow 2 (Succ k)) (n / 2 / power) (n / 2 % power * 2 + n % 2)
    (omega [Nat.modLess (n / 2) power positive, Nat.modLess n 2 (Nat.succNotZero 1)])
    (Eq.trans (Nat.divModEq n 2 (Nat.succNotZero 1))
      (Eq.trans (Eq.cong (half => half * 2 + n % 2) (Nat.divModEq (n / 2) power positive))
        (Nat.regroupHalf (n / 2 / power) power (n / 2 % power) (n % 2))))

-- Two numbers with the same bits above the lowest, and the same lowest bit.
theorem sameHalves (whole: Nat) (other: Nat) (high: Nat) (wholeBit: Nat) (otherBit: Nat) (wholeSplit: whole = high * 2 + wholeBit)
    (otherSplit: other = high * 2 + otherBit) (same: wholeBit = otherBit): whole = other :=
  omega

-- Adding two numbers' low bits as a whole number keeps the parity of their
-- sum.
theorem sumParity (lowX: Nat) (lowY: Nat) (highX: Nat) (highY: Nat) (x: Nat) (y: Nat) (splitX: lowX = highX * 2 + x % 2)
    (splitY: lowY = highY * 2 + y % 2): (lowX + lowY) % 2 = (x + y) % 2 :=
  omega [
    Nat.divModEq x 2 (Nat.succNotZero 1),
    Nat.divModEq y 2 (Nat.succNotZero 1),
    Nat.divModEq (lowX + lowY) 2 (Nat.succNotZero 1),
    Nat.divModEq (x + y) 2 (Nat.succNotZero 1),
    Nat.modLess x 2 (Nat.succNotZero 1),
    Nat.modLess y 2 (Nat.succNotZero 1),
    Nat.modLess (lowX + lowY) 2 (Nat.succNotZero 1),
    Nat.modLess (x + y) 2 (Nat.succNotZero 1)
  ]

-- The low `k` bits of an XOR are the XOR of the low `k` bits.
theorem xorModPow: (k: Nat) → (x: Nat) → (y: Nat) → Nat.xor x y % Nat.pow 2 k = Nat.xor (x % Nat.pow 2 k) (y % Nat.pow 2 k)
  | Zero, x, y =>
    rewrite (omega: x % 1 = 0), (omega: y % 1 = 0), Nat.xorZero 0 0 rfl in
      (omega: Nat.xor x y % 1 = 0)
  | Succ k, x, y =>
    let lowX := x % Nat.pow 2 (Succ k)
    let lowY := y % Nat.pow 2 (Succ k)
    let splitX := modPowSucc x k
    let splitY := modPowSucc y k
    let halfX: lowX / 2 = x / 2 % Nat.pow 2 k := omega [splitX]
    let halfY: lowY / 2 = y / 2 % Nat.pow 2 k := omega [splitY]
    let highs: Nat.xor x y / 2 % Nat.pow 2 k = Nat.xor (x / 2 % Nat.pow 2 k) (y / 2 % Nat.pow 2 k) :=
      Eq.trans (Eq.cong (half => half % Nat.pow 2 k) (Nat.xorDiv x y)) (xorModPow k (x / 2) (y / 2))
    let lowHighs: Nat.xor lowX lowY / 2 = Nat.xor (x / 2 % Nat.pow 2 k) (y / 2 % Nat.pow 2 k) :=
      Eq.trans (Nat.xorDiv lowX lowY) (rewrite halfX, halfY in rfl)
    let whole := Eq.trans (modPowSucc (Nat.xor x y) k) (Eq.cong (high => high * 2 + Nat.xor x y % 2) highs)
    let low :=
      Eq.trans (Nat.divModEq (Nat.xor lowX lowY) 2 (Nat.succNotZero 1)) (Eq.cong (high => high * 2 + Nat.xor lowX lowY % 2) lowHighs)
    let parity :=
      Eq.trans (Nat.xorMod x y)
        (Eq.trans
          (Eq.sym (sumParity lowX lowY (x / 2 % Nat.pow 2 k) (y / 2 % Nat.pow 2 k) x y splitX splitY))
          (Eq.sym (Nat.xorMod lowX lowY)))
    sameHalves (Nat.xor x y % Nat.pow 2 (Succ k)) (Nat.xor lowX lowY) (Nat.xor (x / 2 % Nat.pow 2 k) (y / 2 % Nat.pow 2 k))
      (Nat.xor x y % 2) (Nat.xor lowX lowY % 2) whole low parity

-- The XOR of two numbers below `2 ^ k` is below it.
theorem xorBelow (k: Nat) (x: Nat) (y: Nat) (smallX: x < Nat.pow 2 k) (smallY: y < Nat.pow 2 k): Nat.xor x y < Nat.pow 2 k :=
  let positive := Nat.nonzeroOfPos (Nat.pow 2 k) (Nat.powSuccPos 1 k)
  let kept := xorModPow k x y
  rewrite Nat.modSmall x (Nat.pow 2 k) smallX, Nat.modSmall y (Nat.pow 2 k) smallY at kept in
    rewrite Eq.sym kept in Nat.modLess (Nat.xor x y) (Nat.pow 2 k) positive
