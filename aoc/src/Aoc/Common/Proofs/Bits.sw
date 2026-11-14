--| Facts about `Bits`: `Nat.fromBits`'s lemmas said of the record, a number
--| and its complement, and how appending moves `get` and `width`.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, Eq, List, Nat, Option)

--| A number and its complement add up to the number with a 1 in every
--| position, 2^`width` - 1.
theorem Bits.complementValue ∀ (number: Bits): number.value + number.complement.value + 1 = Nat.pow 2 number.width :=
  Nat.fromBitsFlipped number.bits

--| The first bit is the bit at position 0.
theorem Bits.getZero ∀ (number: Bits): number.get 0 = number.first := match number with
  | { bits = [] } => rfl
  | { bits = [first, ..rest] } => rfl

theorem Bits.widthAppend ∀ (number other: Bits): (number.append other).width = number.width + other.width :=
  List.lengthAppend number.bits other.bits

theorem Bits.emptyAppend ∀ (number: Bits): Bits.empty.append number = number := match number with | { bits } => rfl

--| Appending one bit.
theorem Bits.widthAppendBit ∀ (number: Bits) (bit: Bool):
    (number.append (Bits.cons Bits.empty bit)).width = Succ number.width :=
  rewrite Bits.widthAppend number (Bits.cons Bits.empty bit) in omega

theorem Bits.appendAssoc ∀ (number other third: Bits):
    (number.append other).append third = number.append (other.append third) :=
  Eq.cong (bits => { bits }) (List.appendAssoc number.bits other.bits third.bits)

theorem Bits.getAppendList ∀ (number prefix: List Bool): (prefix.append number).get prefix.length = number.head :=
  match prefix with
    | [] => Bits.getZero { bits = number }
    | [first, ..rest] => Bits.getAppendList number rest

--| The bit after a prefix of `width` bits is the first of what follows it.
theorem Bits.getAppendWidth ∀ (number prefix: Bits): (prefix.append number).get prefix.width = number.first :=
  Bits.getAppendList number.bits prefix.bits

--| A lowest bit in front of the others doubles their number and adds itself.
theorem Bits.valueFromLowFirst ∀ (bit: Bool) (rest: List Bool):
    (Bits.fromLowFirst [bit, ..rest]).value = bit.toNat + (Bits.fromLowFirst rest).value * 2 :=
  rewrite List.reverseCons bit rest, Nat.fromBitsSnoc (List.reverse rest) bit in omega
