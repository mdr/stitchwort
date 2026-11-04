--| Facts about `Bits`, mostly `Nat.fromBits`'s and `Nat.toBits`'s lemmas said
--| of the record, and how appending moves `get` and `width`.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Eq, List, Nat, Option)

--| A number and its complement add up to the number with a 1 in every
--| position, 2^`width` - 1.
theorem Bits.complementValue (number: Bits): number.value + number.complement.value + 1 = Nat.pow 2 number.width :=
  Nat.fromBitsFlipped number.bits

--| A number is below 2^`width`.
theorem Bits.valueBelow (number: Bits): number.value < Nat.pow 2 number.width := Nat.fromBitsBelow number.bits

theorem Bits.widthOfNat (width: Nat) (n: Nat): (Bits.ofNat width n).width = width := Nat.toBitsLength width n

--| The `width` bits of a number that fits in them spell it.
theorem Bits.valueOfNat (width: Nat) (n: Nat) (fits: n < Nat.pow 2 width): (Bits.ofNat width n).value = n := Nat.fromBitsToBits width n fits

--| The bits of `Bits.ofNat` read back.
theorem Bits.ofNatValue: (number: Bits) → Bits.ofNat number.width number.value = number
  | { bits } => Eq.cong (bits => { bits }) (Nat.toBitsFromBits bits)

--| The first bit is the bit at position 0.
theorem Bits.getZero: (number: Bits) → number.get 0 = number.first
  | { bits = [] } => rfl
  | { bits = [first, ..rest] } => rfl

theorem Bits.widthAppend (number: Bits) (other: Bits): (number.append other).width = number.width + other.width :=
  List.lengthAppend number.bits other.bits

theorem Bits.emptyAppend: (number: Bits) → Bits.empty.append number = number
  | { bits } => rfl

--| Appending one bit.
theorem Bits.widthAppendBit (number: Bits) (bit: Bool): (number.append (Bits.cons Bits.empty bit)).width = Succ number.width :=
  rewrite Bits.widthAppend number (Bits.cons Bits.empty bit) in omega

theorem Bits.appendAssoc (number: Bits) (other: Bits) (third: Bits): (number.append other).append third = number.append (other.append third) :=
  Eq.cong (bits => { bits }) (List.appendAssoc number.bits other.bits third.bits)

theorem Bits.getAppendList (number: List Bool): (prefix: List Bool) → List.get (List.append prefix number) (List.length prefix) = List.head number
  | [] => Bits.getZero { bits = number }
  | [first, ..rest] => Bits.getAppendList number rest

--| The bit after a prefix of `width` bits is the first of what follows it.
theorem Bits.getAppendWidth (number: Bits) (prefix: Bits): (prefix.append number).get prefix.width = number.first :=
  Bits.getAppendList number.bits prefix.bits

--| The value of a prefix followed by `other`: the prefix's, shifted left by
--| `other`'s width, plus `other`'s.
theorem Bits.valueAppend (number: Bits) (other: Bits): (number.append other).value = number.value * Nat.pow 2 other.width + other.value :=
  Nat.fromBitsAppend number.bits other.bits
