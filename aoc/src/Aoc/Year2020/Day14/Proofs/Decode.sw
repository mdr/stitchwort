--| Part 2's decoder lists exactly the spec's addresses: an address is in
--| `mask.decode address` if and only if `Spec.Decodes` says the write
--| reaches it. Bit lists first (`decodeBits` against `Spec.allFit`), then
--| numbers through `Nat.fromBits` and `Nat.toBits`.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Void)

--| What `decodeBits` lists fits the mask and the address, bit by bit.
theorem decodedFit ∀ (mask: List MaskBit) (address bits: List Bool)
    (member: bits ∈ decodeBits mask address)
    (same: address.length = mask.length):
    bits.length = mask.length ∧ Spec.allFit mask address bits = True :=
  match mask, address with
    | [], [] =>
      match member with
        | Inl isNil => rewrite <- isNil then Both byComputing byComputing
        | Inr none => none.impossible
    | [Off, ..mask], [bit, ..address] =>
      match List.memMapElim (Cons bit) bits (decodeBits mask address) member with
        | Witness rest (Both inRest built) =>
          match decodedFit mask address rest inRest (arithmetic) with
            | Both length fit => rewrite <- built then Both (arithmetic) (rewrite fit, DecEq.refl bit then byComputing)
    | [On, ..mask], [bit, ..address] =>
      match List.memMapElim (Cons True) bits (decodeBits mask address) member with
        | Witness rest (Both inRest built) =>
          match decodedFit mask address rest inRest (arithmetic) with
            | Both length fit => rewrite <- built then Both (arithmetic) (rewrite fit then byComputing)
    | [X, ..mask], [bit, ..address] =>
      let rest := decodeBits mask address
      match List.memAppend bits (rest.map (Cons False)) (rest.map (Cons True)) member with
        | Inl low =>
          match List.memMapElim (Cons False) bits rest low with
            | Witness tail (Both inRest built) =>
              match decodedFit mask address tail inRest (arithmetic) with
                | Both length fit => rewrite <- built then Both (arithmetic) (rewrite fit then byComputing)
        | Inr high =>
          match List.memMapElim (Cons True) bits rest high with
            | Witness tail (Both inRest built) =>
              match decodedFit mask address tail inRest (arithmetic) with
                | Both length fit => rewrite <- built then Both (arithmetic) (rewrite fit then byComputing)
    | [], [bit, ..address] => Void.impossible arithmetic
    | [maskBit, ..mask], [] => Void.impossible arithmetic

--| Every list of bits that fits the mask and the address is listed.
theorem fitDecoded ∀ (mask: List MaskBit) (address bits: List Bool)
    (sameAddress: address.length = mask.length)
    (sameBits: bits.length = mask.length)
    (fit: Spec.allFit mask address bits = True):
    bits ∈ decodeBits mask address :=
  match mask, address, bits with
    | [], [], [] => Inl byComputing
    | [Off, ..mask], [bit, ..address], [chosen, ..bits] =>
      rewrite fit.left.read then
        List.memMap
          (decodeBits mask address)
          bits
          (fitDecoded mask address bits (arithmetic) (arithmetic) fit.right)
          (Cons bit)
    | [On, ..mask], [bit, ..address], [chosen, ..bits] =>
      rewrite fit.left then
        List.memMap
          (decodeBits mask address)
          bits
          (fitDecoded mask address bits (arithmetic) (arithmetic) fit.right)
          (Cons True)
    | [X, ..mask], [bit, ..address], [chosen, ..bits] =>
      let rest := decodeBits mask address
      let inRest := fitDecoded mask address bits (arithmetic) (arithmetic) fit.right
      match chosen with
        | False =>
          List.memAppendLeft
            [False, ..bits]
            (rest.map (Cons False))
            (rest.map (Cons True))
            (List.memMap rest bits inRest (Cons False))
        | True =>
          List.memAppendRight
            [True, ..bits]
            (rest.map (Cons False))
            (rest.map (Cons True))
            (List.memMap rest bits inRest (Cons True))
    | [], [], [chosen, ..bits] => Void.impossible arithmetic
    | [], [bit, ..address], bits => Void.impossible arithmetic
    | [maskBit, ..mask], [], bits => Void.impossible arithmetic
    | [maskBit, ..mask], [bit, ..address], [] => Void.impossible arithmetic

theorem decodeSound ∀ (mask: Mask) (address target: Nat)
    (member: target ∈ mask.decode address):
    Spec.Decodes mask address target = True :=
  let width := mask.bits.length
  match List.memMapElim Nat.fromBits target (decodeBits mask.bits (Nat.toBits width address)) member with
    | Witness bits (Both listed built) =>
      match decodedFit mask.bits (Nat.toBits width address) bits listed (Nat.toBitsLength width address) with
        | Both length fit =>
          let below: Nat.fromBits bits < Nat.pow 2 width := rewrite length at Nat.fromBitsBelow bits
          let back: Nat.toBits width (Nat.fromBits bits) = bits := rewrite length at Nat.toBitsFromBits bits
          rewrite <- built then
            match small: Nat.fromBits bits < Nat.pow 2 width with
              | True => rewrite back, fit then byComputing

theorem decodeComplete ∀ (mask: Mask) (address target: Nat)
    (decodes: Spec.Decodes mask address target = True):
    target ∈ mask.decode address :=
  let width := mask.bits.length
  let below: target < Nat.pow 2 width := arithmetic [decodes.left]
  let listed :=
    fitDecoded mask.bits
      (Nat.toBits width address)
      (Nat.toBits width target)
      (Nat.toBitsLength width address)
      (Nat.toBitsLength width target)
      decodes.right
  rewrite <- Nat.fromBitsToBits width target below then List.memMap _ (Nat.toBits width target) listed Nat.fromBits

--| The decoder's list holds an address exactly when the spec's write reaches it.
theorem decodeContains ∀ (mask: Mask) (address target: Nat):
    (mask.decode address).contains target = Spec.Decodes mask address target :=
  match decodes: Spec.Decodes mask address target with
    | True => decodeComplete mask address target decodes
    | False =>
      match contains: (mask.decode address).contains target with
        | True =>
          Void.impossible
            (Bool.trueNotFalse (Eq.trans (Eq.flipped (decodeSound mask address target contains.read)) decodes))
        | False => byComputing
