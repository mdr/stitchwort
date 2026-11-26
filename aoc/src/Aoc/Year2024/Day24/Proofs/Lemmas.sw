--| General facts the proofs use: bits of small numbers.

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Common (Bits)
import Aoc.Common.Proofs (..)
import Aoc.Year2024.Day24 (..)
import Std (Bool, Eq, Exists, List, Map, Nat, Option, Ord, Void)

--| A number below `2 ^ bit` has bit `bit` clear.
theorem testBitSmall ∀ (n bit: Nat) (small: n < Nat.pow 2 bit): n.testBit bit = False :=
  rewrite Nat.testBitDiv n bit, Nat.divSmall n (Nat.pow 2 bit) small

--| A number below `2 ^ bits` has every bit from `bits` up clear.
theorem testBitAbove ∀ (n bits bit: Nat) (small: n < Nat.pow 2 bits) (above: bits ≤ bit): n.testBit bit = False :=
  testBitSmall n bit (arithmetic [Nat.powMono 1 bits bit above])

--| What `Map.lookupLast` finds is one of the pairs.
theorem lookupLastMem ∀ [auto ord: Ord k] (key: k) (value: v) (pairs: List (k, v))
    (found: Map.lookupLast key pairs = Some value):
    (key, value) ∈ pairs :=
  match pairs with
    | [(other, otherValue), ..rest] =>
      match later: Map.lookupLast key rest with
        | Some laterValue => Inr (lookupLastMem key value rest (Eq.trans later found))
        | None =>
          match same: Ord.compare key other with
            | Equal => Inl (rewrite ord.equal key other same, Option.someInjective found)

--| The lowest bit of a number written lowest first, and the rest.
theorem fromBitsLow ∀ (bit: Bool) (rest: List Bool): Nat.testBit ((Bits.fromLowFirst [bit, ..rest]).value) 0 = bit :=
  rewrite Bits.valueFromLowFirst bit rest,
      testBitZero (Bool.toNat bit + (Bits.fromLowFirst rest).value * 2),
      Nat.modAddMul bit.toNat (Bits.fromLowFirst rest).value 2 then
    Bool.toNatOdd bit

theorem fromBitsHigh ∀ (bit: Bool) (rest: List Bool) (index: Nat):
    Nat.testBit ((Bits.fromLowFirst [bit, ..rest]).value) (Succ index)
      = Nat.testBit ((Bits.fromLowFirst rest).value) index :=
  rewrite Bits.valueFromLowFirst bit rest,
      Nat.testBitSucc (Bool.toNat bit + (Bits.fromLowFirst rest).value * 2) index,
      (arithmetic [Bool.toNatLeOne bit]: (Bool.toNat bit + (Bits.fromLowFirst rest).value * 2) / 2
        = (Bits.fromLowFirst rest).value)

--| The bits `allSome` gives for a range: below the range's length, bit `k`
--| of the number is what `f` gives for the range's `k`th number.
theorem rangeBits ∀ (f: Nat → Option Bool):
    ∀ (count start: Nat) (bits: List Bool) => List.allSome ((List.rangeFrom count start).map f) = Some bits
      → ∀ (k: Nat) => k < count
        → ∃ (value: Bool) => f (k + start) = Some value ∧ Nat.testBit ((Bits.fromLowFirst bits).value) k = value
  | Zero, start, bits, all, k, below => Void.impossible arithmetic
  | Succ count, start, bits, all, k, below =>
    Option.flatMapEqSome
      (f start)
      (value => List.allSome ((List.rangeFrom count (Succ start)).map f) |> .map (Cons value))
      bits
      all
      (value isValue rest =>
        Option.mapEqSome
          (List.allSome ((List.rangeFrom count (Succ start)).map f))
          (Cons value)
          bits
          rest
          (restBits restIs isBits =>
            match k with
              | Zero => Witness value (Both isValue (rewrite <- isBits then fromBitsLow value restBits))
              | Succ index =>
                match rangeBits f count (Succ start) restBits restIs index (arithmetic) with
                  | Witness found (Both foundIs bitIs) =>
                    Witness found
                      (Both
                        (rewrite (arithmetic: Succ index + start = index + Succ start) then foundIs)
                        (rewrite <- isBits, fromBitsHigh value restBits index then bitIs))))

--| From the range's length up, every bit is clear.
theorem rangeBitsBeyond ∀ (f: Nat → Option Bool):
    ∀ (count start: Nat) (bits: List Bool) => List.allSome ((List.rangeFrom count start).map f) = Some bits
      → ∀ (k: Nat) => count ≤ k → Nat.testBit ((Bits.fromLowFirst bits).value) k = False
  | Zero, start, bits, all, k, above => rewrite <- Option.someInjective all
  | Succ count, start, bits, all, k, above =>
    Option.flatMapEqSome
      (f start)
      (value => List.allSome ((List.rangeFrom count (Succ start)).map f) |> .map (Cons value))
      bits
      all
      (value isValue rest =>
        Option.mapEqSome
          (List.allSome ((List.rangeFrom count (Succ start)).map f))
          (Cons value)
          bits
          rest
          (restBits restIs isBits =>
            match k with
              | Succ index =>
                rewrite <- isBits, fromBitsHigh value restBits index then
                  rangeBitsBeyond f count (Succ start) restBits restIs index (arithmetic)))

--| `bitCount` from any start.
def countFrom (bitOf: Wire → Option Nat) (start: Nat) (wires: List Wire): Nat :=
  wires.foldLeft start (count wire => bitOf wire |> .fold count (bit => Nat.max count (bit + 1)))

theorem countFromAtLeast ∀ (bitOf: Wire → Option Nat) (wires: List Wire) (start: Nat):
    start ≤ countFrom bitOf start wires :=
  match wires with
    | [] => Nat.leRefl start
    | [wire, ..rest] =>
      match found: bitOf wire with
        | None => countFromAtLeast bitOf rest start
        | Some bit => arithmetic [Nat.leMaxLeft start (bit + 1), countFromAtLeast bitOf rest (Nat.max start (bit + 1))]

--| Every bit `bitOf` finds among the wires is below their count.
theorem countFromAbove ∀ (bitOf: Wire → Option Nat) (wire: Wire) (bit: Nat)
    (isBit: bitOf wire = Some bit)
    (wires: List Wire) (start: Nat)
    (member: wire ∈ wires):
    bit < countFrom bitOf start wires :=
  match wires, member with
    | [], member => member.impossible
    | [other, ..rest], Inl same =>
      rewrite same, isBit then
        arithmetic [Nat.leMaxRight start (bit + 1), countFromAtLeast bitOf rest (Nat.max start (bit + 1))]
    | [other, ..rest], Inr later => countFromAbove bitOf wire bit isBit rest _ later
