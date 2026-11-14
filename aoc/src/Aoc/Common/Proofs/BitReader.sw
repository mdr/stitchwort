--| Facts about `BitReader`: what a read takes off the front of the unread
--| bits, and that reading a field written in the right width gives the
--| field back.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair)

--| `Some` of two pairs: the same parts.
theorem somePairInjective ∀ [x1: a] [y1: b] [x2: a] [y2: b] (h: Some (x1, y1) = Some (x2, y2)): x1 = x2 ∧ y1 = y2 :=
  let both := Option.someInjective h
  Both (Pair.mkInjectiveFst both) (Pair.mkInjectiveSnd both)

--| A field of the right width at the front is read, and the rest is left.
theorem BitReader.readAppend ∀ (field rest: List Bool) (width: Nat)
    (length: field.length = width):
    BitReader.read { unread = field ++ rest } width = Some ({ bits = field }, { unread = rest }) :=
  rewrite List.takeAppendLength field rest width length,
      List.dropAppendLength field rest width length,
      length,
      DecEq.refl width in
    rfl

--| What a read takes is the front of the unread bits, in the width asked.
theorem BitReader.readSome ∀ (reader: BitReader) (width: Nat) (field: Bits) (rest: BitReader)
    (read: reader.read width = Some (field, rest)):
    reader.unread = field.bits ++ rest.unread ∧ field.width = width :=
  let taken := reader.unread.take width
  let unfolded: (if taken.length == width then Some ({ bits = taken }, { unread = reader.unread.drop width }) else None)
    = Some (field, rest) :=
    read
  match e: taken.length == width with
    | True =>
      let parts := somePairInjective unfolded
      rewrite <- parts.left, <- parts.right in Both (Eq.sym (List.appendTakeDrop reader.unread width)) e.read

--| A number that fits its width is read back from its bits.
theorem BitReader.readNumberAppend ∀ (width n: Nat) (rest: List Bool)
    (small: n < Nat.pow 2 width):
    BitReader.readNumber { unread = Nat.toBits width n ++ rest } width = Some (n, { unread = rest }) :=
  rewrite BitReader.readAppend (Nat.toBits width n) rest width (Nat.toBitsLength width n),
      Nat.fromBitsToBits width n small in
    rfl

--| What a read takes spells a number that fits the width: the unread bits
--| start with the number in that many bits.
theorem BitReader.readValue ∀ (reader: BitReader) (width: Nat) (field: Bits) (rest: BitReader)
    (read: reader.read width = Some (field, rest)):
    reader.unread = Nat.toBits width field.value ++ rest.unread ∧ field.value < Nat.pow 2 width :=
  let split := BitReader.readSome reader width field rest read
  let written := Nat.toBitsFromBits field.bits
  rewrite split.right at written in
    Both (rewrite written in split.left) (rewrite split.right at (Nat.fromBitsBelow field.bits))

--| What a number read is the number's bits at the front of the unread
--| bits, and the number fits.
theorem BitReader.readNumberSome ∀ (reader: BitReader) (width n: Nat) (rest: BitReader)
    (read: reader.readNumber width = Some (n, rest)):
    reader.unread = Nat.toBits width n ++ rest.unread ∧ n < Nat.pow 2 width :=
  match e: reader.read width with
    | Some (field, after) =>
      let parts := somePairInjective read
      rewrite <- parts.left, <- parts.right in BitReader.readValue reader width field after e

--| The bit a read takes is the front of the unread bits.
theorem BitReader.readBitSome ∀ (reader: BitReader) (bit: Bool) (rest: BitReader)
    (read: reader.readBit = Some (bit, rest)):
    reader.unread = [bit, ..rest.unread] :=
  match reader with
    | { unread = [first, ..others] } =>
      let parts := somePairInjective read
      rewrite <- parts.left, <- parts.right in rfl
