--| Part 1's mask, applied with `Nat.and` and `Nat.or`, is the spec's bit by
--| bit overwrite: the bits of an `and` and an `or` are those of the numbers
--| zipped, and both stay below a power of 2 the numbers stay below.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14 (Spec)
import Std (Bool, Eq, List, Nat, Void)

theorem zipWithSnoc (f: a → b → c) (x: a) (y: b): (xs: List a) → (ys: List b) → xs.length = ys.length →
    List.zipWith (xs ++ [x]) (ys ++ [y]) f = List.zipWith xs ys f ++ [f x y]
  | [], [], same => rfl
  | [first, ..xs], [second, ..ys], same => rewrite zipWithSnoc f x y xs ys (omega) in rfl
  | [], [second, ..ys], same => Void.exfalso (omega)
  | [first, ..xs], [], same => Void.exfalso (omega)

theorem lastBitAnd (m: Nat) (n: Nat): (Nat.and m n % 2 == 1) = (m % 2 == 1 && n % 2 == 1) := rewrite Nat.andMod m n in Nat.oddProduct m n

theorem lastBitOr (m: Nat) (n: Nat): (Nat.or m n % 2 == 1) = (m % 2 == 1 || n % 2 == 1) := rewrite Nat.orMod m n in Nat.oddEither m n

theorem toBitsAnd: (width: Nat) → (m: Nat) → (n: Nat) →
    Nat.toBits width (Nat.and m n) = List.zipWith (Nat.toBits width m) (Nat.toBits width n) (a b => a && b)
  | 0, m, n => rfl
  | Succ width, m, n =>
    rewrite lastBitAnd m n, Nat.andDiv m n, toBitsAnd width (m / 2) (n / 2) in
      Eq.sym
        (zipWithSnoc (a b => a && b) (m % 2 == 1) (n % 2 == 1) (Nat.toBits width (m / 2)) (Nat.toBits width (n / 2))
          (rewrite Nat.toBitsLength width (m / 2), Nat.toBitsLength width (n / 2) in rfl))

theorem toBitsOr: (width: Nat) → (m: Nat) → (n: Nat) →
    Nat.toBits width (Nat.or m n) = List.zipWith (Nat.toBits width m) (Nat.toBits width n) (a b => a || b)
  | 0, m, n => rfl
  | Succ width, m, n =>
    rewrite lastBitOr m n, Nat.orDiv m n, toBitsOr width (m / 2) (n / 2) in
      Eq.sym
        (zipWithSnoc (a b => a || b) (m % 2 == 1) (n % 2 == 1) (Nat.toBits width (m / 2)) (Nat.toBits width (n / 2))
          (rewrite Nat.toBitsLength width (m / 2), Nat.toBitsLength width (n / 2) in rfl))

theorem lowBitAnd (m: Nat) (n: Nat): m * n % 2 ≤ n % 2 :=
  let below := Nat.modLess n 2 (Nat.succNotZero 1)
  rewrite Eq.sym (Nat.mulModMod m n 2) in
    match e: n % 2 with
      | 0 => rewrite Nat.mulZero m in omega
      | 1 => rewrite Nat.mulOne m in omega [Nat.modLess m 2 (Nat.succNotZero 1)]
      | Succ (Succ k) => Void.exfalso (omega)

theorem andLe (m: Nat) (n: Nat): Nat.and m n ≤ n
    decreasing m + n
:=
  match some: Nat.leq (m + n) 0 with
    | True => rewrite Nat.andZero m n some in omega
    | False =>
      rewrite Nat.andSome m n some in
        omega [andLe (m / 2) (n / 2) [decreasing := Nat.halvesLess m n some], Nat.divModEq n 2 (Nat.succNotZero 1), lowBitAnd m n]

theorem orBelow: (k: Nat) → (m: Nat) → (n: Nat) → m < Nat.pow 2 k → n < Nat.pow 2 k → Nat.or m n < Nat.pow 2 k
  | 0, m, n, smallM, smallN => rewrite (omega: m = 0), (omega: n = 0) in rfl
  | Succ k, m, n, smallM, smallN =>
    let power := Nat.powSucc 2 k
    let half := orBelow k (m / 2) (n / 2) (omega [power]) (omega [power])
    omega [Nat.divModEq (Nat.or m n) 2 (Nat.succNotZero 1), Nat.orDiv m n, Nat.modLess (Nat.or m n) 2 (Nat.succNotZero 1), power, half]

theorem maskedBits: (mask: List MaskBit) → (value: List Bool) → value.length = mask.length →
    List.zipWith (List.zipWith value (mask.map MaskBit.isFloating) (a b => a && b)) (mask.map MaskBit.isOn) (a b => a || b)
      = List.zipWith mask value Spec.overwrite
  | [], [], same => rfl
  | [bit, ..mask], [first, ..value], same => rewrite maskedBits mask value (omega) in cases
  | [], [first, ..value], same => Void.exfalso (omega)
  | [bit, ..mask], [], same => Void.exfalso (omega)

--| Part 1's rule is the puzzle's: `applyTo` overwrites each bit as the spec does.
theorem applyToMasked (mask: Mask) (value: Nat): mask.applyTo value = Spec.masked mask value :=
  let width := mask.bits.length
  let floatingRaw := Nat.toBitsFromBits (mask.bits.map MaskBit.isFloating)
  let floatingBits: Nat.toBits width mask.floating = mask.bits.map MaskBit.isFloating := rewrite List.lengthMap mask.bits MaskBit.isFloating at floatingRaw in floatingRaw
  let onesRaw := Nat.toBitsFromBits (mask.bits.map MaskBit.isOn)
  let onesBits: Nat.toBits width mask.ones = mask.bits.map MaskBit.isOn := rewrite List.lengthMap mask.bits MaskBit.isOn at onesRaw in onesRaw
  let floatingBelow: mask.floating < Nat.pow 2 width := rewrite List.lengthMap mask.bits MaskBit.isFloating at Nat.fromBitsBelow (mask.bits.map MaskBit.isFloating)
  let onesBelow: mask.ones < Nat.pow 2 width := rewrite List.lengthMap mask.bits MaskBit.isOn at Nat.fromBitsBelow (mask.bits.map MaskBit.isOn)
  let kept := Nat.and value mask.floating
  let below: mask.applyTo value < Nat.pow 2 width := orBelow width kept mask.ones (omega [andLe value mask.floating, floatingBelow]) onesBelow
  let bits: Nat.toBits width (mask.applyTo value) = List.zipWith mask.bits (Nat.toBits width value) Spec.overwrite :=
    rewrite toBitsOr width kept mask.ones, toBitsAnd width value mask.floating, floatingBits, onesBits in
      maskedBits mask.bits (Nat.toBits width value) (Nat.toBitsLength width value)
  Eq.trans (Eq.sym (Nat.fromBitsToBits width (mask.applyTo value) below)) (Eq.cong Nat.fromBits bits)
