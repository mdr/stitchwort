--| General facts the proofs use: bits of small numbers.

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Common (Bits)
import Aoc.Common.Proofs (..)
import Aoc.Year2024.Day24 (..)
import Std (Bool, Eq, Exists, List, Map, Nat, Option, Ord, Void)

--| A number below `2 ^ bit` has bit `bit` clear.
theorem testBitSmall ∀ (n: Nat) (bit: Nat) (small: n < Nat.pow 2 bit): n.testBit bit = False :=
  rewrite Nat.testBitDiv n bit, Nat.divSmall n (Nat.pow 2 bit) small in rfl

--| A number below `2 ^ bits` has every bit from `bits` up clear.
theorem testBitAbove ∀ (n: Nat) (bits: Nat) (bit: Nat) (small: n < Nat.pow 2 bits) (above: bits ≤ bit): n.testBit bit = False :=
  testBitSmall n bit (omega [Nat.powMono 1 bits bit above])

--| What `Map.lookupLast` finds is one of the pairs.
theorem lookupLastMem ∀ [auto ord: Ord k] (key: k) (value: v) (pairs: List (k, v)) (found: Map.lookupLast key pairs = Some value): (key, value) ∈ pairs :=
  match pairs with
    | [(other, otherValue), ..rest] =>
      match later: Map.lookupLast key rest with
        | Some laterValue => Inr (lookupLastMem key value rest (Eq.trans later found))
        | None =>
          match same: Ord.compare key other with
            | Equal => Inl (rewrite ord.equal key other same, Option.someInjective found in rfl)

--| The lowest bit of a number written lowest first, and the rest.
theorem fromBitsLow ∀ (bit: Bool) (rest: List Bool): Nat.testBit ((Bits.fromLowFirst [bit, ..rest]).value) 0 = bit :=
  rewrite Bits.valueFromLowFirst bit rest, testBitZero (Bool.toNat bit + (Bits.fromLowFirst rest).value * 2), Nat.modAddMul bit.toNat (Bits.fromLowFirst rest).value 2 in Bool.toNatOdd bit

theorem fromBitsHigh ∀ (bit: Bool) (rest: List Bool) (index: Nat): Nat.testBit ((Bits.fromLowFirst [bit, ..rest]).value) (Succ index) = Nat.testBit ((Bits.fromLowFirst rest).value) index :=
  rewrite Bits.valueFromLowFirst bit rest, Nat.testBitSucc (Bool.toNat bit + (Bits.fromLowFirst rest).value * 2) index, (omega [Bool.toNatLeOne bit]: (Bool.toNat bit + (Bits.fromLowFirst rest).value * 2) / 2 = (Bits.fromLowFirst rest).value) in rfl

--| The bits `allSome` gives for a range: below the range's length, bit `k`
--| of the number is what `f` gives for the range's `k`th number.
theorem rangeBits ∀ (f: Nat → Option Bool): ∀ (count start: Nat) (bits: List Bool) => List.allSome ((List.rangeFrom count start).map f) = Some bits →
    ∀ (k: Nat) => k < count → ∃ (value: Bool) => f (k + start) = Some value ∧ Nat.testBit ((Bits.fromLowFirst bits).value) k = value
  | Zero, start, bits, all, k, below => Void.exfalso (omega)
  | Succ count, start, bits, all, k, below =>
    Option.flatMapEqSome (f start) (value => List.allSome ((List.rangeFrom count (Succ start)).map f) |> .map (Cons value)) bits all (value isValue rest =>
      Option.mapEqSome (List.allSome ((List.rangeFrom count (Succ start)).map f)) (Cons value) bits rest (restBits restIs isBits =>
        match k with
          | Zero => Witness value (Both isValue (rewrite <- isBits in fromBitsLow value restBits))
          | Succ index =>
            match rangeBits f count (Succ start) restBits restIs index (omega) with
              | Witness found (Both foundIs bitIs) =>
                Witness found (Both (rewrite (omega: Succ index + start = index + Succ start) in foundIs) (rewrite <- isBits, fromBitsHigh value restBits index in bitIs))))

--| From the range's length up, every bit is clear.
theorem rangeBitsBeyond ∀ (f: Nat → Option Bool): ∀ (count start: Nat) (bits: List Bool) => List.allSome ((List.rangeFrom count start).map f) = Some bits →
    ∀ (k: Nat) => count ≤ k → Nat.testBit ((Bits.fromLowFirst bits).value) k = False
  | Zero, start, bits, all, k, above => rewrite <- Option.someInjective all in rfl
  | Succ count, start, bits, all, k, above =>
    Option.flatMapEqSome (f start) (value => List.allSome ((List.rangeFrom count (Succ start)).map f) |> .map (Cons value)) bits all (value isValue rest =>
      Option.mapEqSome (List.allSome ((List.rangeFrom count (Succ start)).map f)) (Cons value) bits rest (restBits restIs isBits =>
        match k with
          | Succ index => rewrite <- isBits, fromBitsHigh value restBits index in rangeBitsBeyond f count (Succ start) restBits restIs index (omega)))

--| `bitCount` from any start.
def countFrom (bitOf: Wire → Option Nat) (start: Nat) (wires: List Wire): Nat :=
  wires.foldLeft start (count wire => bitOf wire |> .fold count (bit => Nat.max count (bit + 1)))

theorem maxAtLeast ∀ (m: Nat) (n: Nat): m ≤ Nat.max m n ∧ n ≤ Nat.max m n := match below: Nat.leq m n with
  | True => Both below (Nat.leRefl n)
  | False => Both (Nat.leRefl m) (omega)

theorem countFromAtLeast ∀ (bitOf: Wire → Option Nat) (wires: List Wire) (start: Nat): start ≤ countFrom bitOf start wires :=
  match wires with
    | [] => Nat.leRefl start
    | [wire, ..rest] =>
      match found: bitOf wire with
        | None => countFromAtLeast bitOf rest start
        | Some bit => omega [(maxAtLeast start (bit + 1)).left, countFromAtLeast bitOf rest (Nat.max start (bit + 1))]

--| Every bit `bitOf` finds among the wires is below their count.
theorem countFromAbove ∀ (bitOf: Wire → Option Nat) (wire: Wire) (bit: Nat) (isBit: bitOf wire = Some bit)
    (wires: List Wire) (start: Nat) (member: wire ∈ wires): bit < countFrom bitOf start wires :=
  match wires, member with
    | [], member => Void.exfalso member
    | [other, ..rest], Inl same =>
      rewrite same in
        rewrite isBit in
          omega [(maxAtLeast start (bit + 1)).right, countFromAtLeast bitOf rest (Nat.max start (bit + 1))]
    | [other, ..rest], Inr later => countFromAbove bitOf wire bit isBit rest _ later
