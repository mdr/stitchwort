--| Part 1's mask, applied with `Nat.and` and `Nat.or`, is the spec's bit by
--| bit overwrite: the bits of an `and` and an `or` are those of the numbers
--| zipped, and both stay below a power of 2 the numbers stay below.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14 (Spec)
import Std (Bool, Eq, List, Nat, Void)

theorem maskedBits (mask: List MaskBit) (value: List Bool) (same: value.length = mask.length): List.zipWith (List.zipWith value (mask.map MaskBit.isFloating) (a b => a && b)) (mask.map MaskBit.isOn) (a b => a || b)
    = List.zipWith mask value Spec.overwrite := match mask, value with
      | [], [] => rfl
      | [bit, ..mask], [first, ..value] => rewrite maskedBits mask value (omega) in cases
      | [], [first, ..value] => Void.exfalso (omega)
      | [bit, ..mask], [] => Void.exfalso (omega)

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
  let below: mask.applyTo value < Nat.pow 2 width := Nat.orBelow width kept mask.ones (omega [Nat.andLeRight value mask.floating, floatingBelow]) onesBelow
  let bits: Nat.toBits width (mask.applyTo value) = List.zipWith mask.bits (Nat.toBits width value) Spec.overwrite :=
    rewrite Nat.toBitsOr width kept mask.ones, Nat.toBitsAnd width value mask.floating, floatingBits, onesBits in
      maskedBits mask.bits (Nat.toBits width value) (Nat.toBitsLength width value)
  Eq.trans (Eq.sym (Nat.fromBitsToBits width (mask.applyTo value) below)) (Eq.cong Nat.fromBits bits)
