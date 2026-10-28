-- General facts the proofs use: bits of small numbers, and `List.all` on
-- a member.

namespace Aoc.Year2024.Day24.Proofs
import Aoc.Year2024.Day24 (..)
import Std (Bool, Eq, Exists, List, Map, Nat, Option, Ord, Void)

-- A number below `2 ^ bit` has bit `bit` clear.
theorem testBitSmall (n: Nat) (bit: Nat) (small: n < Nat.pow 2 bit): Nat.testBit n bit = False :=
  let positive := Nat.nonzeroOfPos (Nat.pow 2 bit) (Nat.powSuccPos 1 bit)
  rewrite Nat.testBitDiv n bit, Nat.divSmall n (Nat.pow 2 bit) [ok := positive] small in rfl

-- A number below `2 ^ bits` has every bit from `bits` up clear.
theorem testBitAbove (n: Nat) (bits: Nat) (bit: Nat) (small: n < Nat.pow 2 bits) (above: bits ≤ bit): Nat.testBit n bit = False :=
  testBitSmall n bit (omega [Nat.powMono 1 bits bit above])

-- `List.all` holds of each member.
theorem allMember (p: a → Bool) (xs: List a) (x: a) (all: List.all xs p = True) (member: x ∈ xs): p x = True :=
  List.allMem (y => p y = True) x xs (List.allToAll p xs all) member

-- What `Map.lookupLast` finds is one of the pairs.
theorem lookupLastMem [auto ord: Ord k] (key: k) (value: v): (pairs: List (k, v)) → Map.lookupLast key pairs = Some value → (key, value) ∈ pairs
  | Nil, found => Void.exfalso (Option.noneNotSome value found)
  | Cons (other, otherValue) rest, found =>
    match later: Map.lookupLast key rest with
      | Some laterValue => Inr (lookupLastMem key value rest (Eq.trans later found))
      | None =>
        match same: Ord.compare key other with
          | Equal => Inl (rewrite ord.equal key other same, Option.someInjective otherValue value found in rfl)
          | Less => Void.exfalso (Option.noneNotSome value found)
          | Greater => Void.exfalso (Option.noneNotSome value found)

-- What `List.findMap` finds, `f` gives for some element.
theorem findMapSome (f: a → Option b) (result: b): (xs: List a) → List.findMap xs f = Some result → ∃ (x: a) => f x = Some result
  | Nil, found => Void.exfalso (Option.noneNotSome result found)
  | Cons x rest, found =>
    match here: f x with
      | Some value => Witness x (Eq.trans here found)
      | None => findMapSome f result rest found

theorem toNatSmall: (bit: Bool) → bit.toNat < 2
  | False => omega
  | True => omega

-- The lowest bit of `fromBits`, and the rest.
theorem fromBitsLow (bit: Bool) (rest: List Bool): Nat.testBit (fromBits (Cons bit rest)) 0 = bit :=
  rewrite testBitZero (fromBits (Cons bit rest)), Nat.modAddMul bit.toNat (fromBits rest) 2 in toNatOdd bit

theorem fromBitsHigh (bit: Bool) (rest: List Bool) (index: Nat): Nat.testBit (fromBits (Cons bit rest)) (Succ index) = Nat.testBit (fromBits rest) index :=
  rewrite Nat.testBitSucc (fromBits (Cons bit rest)) index, (omega [toNatSmall bit]: (bit.toNat + fromBits rest * 2) / 2 = fromBits rest) in rfl

-- The bits `allSome` gives for a range: below the range's length, bit `k`
-- of `fromBits` is what `f` gives for the range's `k`th number.
theorem rangeBits (f: Nat → Option Bool): (count: Nat) → (start: Nat) → (bits: List Bool) → allSome ((List.rangeFrom count start).map f) = Some bits →
    (k: Nat) → k < count → ∃ (value: Bool) => f (k + start) = Some value ∧ Nat.testBit (fromBits bits) k = value
  | Zero, start, bits, all, k, below => Void.exfalso (omega)
  | Succ count, start, bits, all, k, below =>
    Option.flatMapEqSome (f start) (value => allSome ((List.rangeFrom count (Succ start)).map f) |> .map (Cons value)) bits all (value isValue rest =>
      Option.mapEqSome (allSome ((List.rangeFrom count (Succ start)).map f)) (Cons value) bits rest (restBits restIs isBits =>
        match k with
          | Zero => Witness value (Both isValue (rewrite <- isBits in fromBitsLow value restBits))
          | Succ index =>
            match rangeBits f count (Succ start) restBits restIs index (omega) with
              | Witness found (Both foundIs bitIs) =>
                Witness found (Both (rewrite (omega: Succ index + start = index + Succ start) in foundIs) (rewrite <- isBits, fromBitsHigh value restBits index in bitIs))))

-- From the range's length up, every bit is clear.
theorem rangeBitsBeyond (f: Nat → Option Bool): (count: Nat) → (start: Nat) → (bits: List Bool) → allSome ((List.rangeFrom count start).map f) = Some bits →
    (k: Nat) → count ≤ k → Nat.testBit (fromBits bits) k = False
  | Zero, start, bits, all, k, above => rewrite <- Option.someInjective Nil bits all in rfl
  | Succ count, start, bits, all, k, above =>
    Option.flatMapEqSome (f start) (value => allSome ((List.rangeFrom count (Succ start)).map f) |> .map (Cons value)) bits all (value isValue rest =>
      Option.mapEqSome (allSome ((List.rangeFrom count (Succ start)).map f)) (Cons value) bits rest (restBits restIs isBits =>
        match k with
          | Zero => Void.exfalso (omega)
          | Succ index => rewrite <- isBits, fromBitsHigh value restBits index in rangeBitsBeyond f count (Succ start) restBits restIs index (omega)))

-- `bitCount` from any start.
def countFrom (bitOf: Wire → Option Nat) (start: Nat) (wires: List Wire): Nat :=
  wires.foldLeft start (count wire => bitOf wire |> .fold count (bit => Nat.max count (bit + 1)))

theorem maxAtLeast (m: Nat) (n: Nat): m ≤ Nat.max m n ∧ n ≤ Nat.max m n :=
  match below: Nat.leq m n with
    | True => Both below (Nat.leRefl n)
    | False => Both (Nat.leRefl m) (omega)

theorem countFromAtLeast (bitOf: Wire → Option Nat): (wires: List Wire) → (start: Nat) → start ≤ countFrom bitOf start wires
  | Nil, start => Nat.leRefl start
  | Cons wire rest, start =>
    match found: bitOf wire with
      | None => countFromAtLeast bitOf rest start
      | Some bit => omega [(maxAtLeast start (bit + 1)).left, countFromAtLeast bitOf rest (Nat.max start (bit + 1))]

-- Every bit `bitOf` finds among the wires is below their count.
theorem countFromAbove (bitOf: Wire → Option Nat) (wire: Wire) (bit: Nat) (isBit: bitOf wire = Some bit):
    (wires: List Wire) → (start: Nat) → wire ∈ wires → bit < countFrom bitOf start wires
  | Nil, start, member => Void.exfalso member
  | Cons other rest, start, Inl same =>
    rewrite same in
      rewrite isBit in
        omega [(maxAtLeast start (bit + 1)).right, countFromAtLeast bitOf rest (Nat.max start (bit + 1))]
  | Cons other rest, start, Inr later => countFromAbove bitOf wire bit isBit rest _ later
