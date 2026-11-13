--| Part 2's decoder lists exactly the spec's addresses: an address is in
--| `mask.decode address` if and only if `Spec.Decodes` says the write
--| reaches it. Bit lists first (`decodeBits` against `Spec.allFit`), then
--| numbers through `Nat.fromBits` and `Nat.toBits`.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Void)

--| What `decodeBits` lists fits the mask and the address, bit by bit.
theorem decodedFit ∀ (mask: List MaskBit) (address bits: List Bool) (member: bits ∈ decodeBits mask address)
    (same: address.length = mask.length): bits.length = mask.length ∧ Spec.allFit mask address bits = True :=
  match mask, address with
    | [], [] =>
      match member with
        | Inl isNil => rewrite <- isNil in Both rfl rfl
        | Inr none => Void.exfalso none
    | [Off, ..mask], [bit, ..address] =>
      match List.memMapElim (Cons bit) bits (decodeBits mask address) member with
        | Witness rest (Both inRest built) =>
          match decodedFit mask address rest inRest (omega) with
            | Both length fit => rewrite <- built in Both (omega) (rewrite fit, DecEq.refl bit in rfl)
    | [On, ..mask], [bit, ..address] =>
      match List.memMapElim (Cons True) bits (decodeBits mask address) member with
        | Witness rest (Both inRest built) =>
          match decodedFit mask address rest inRest (omega) with
            | Both length fit => rewrite <- built in Both (omega) (rewrite fit in rfl)
    | [X, ..mask], [bit, ..address] =>
      let rest := decodeBits mask address
      match List.memAppend bits (rest.map (Cons False)) (rest.map (Cons True)) member with
        | Inl low =>
          match List.memMapElim (Cons False) bits rest low with
            | Witness tail (Both inRest built) =>
              match decodedFit mask address tail inRest (omega) with
                | Both length fit => rewrite <- built in Both (omega) (rewrite fit in rfl)
        | Inr high =>
          match List.memMapElim (Cons True) bits rest high with
            | Witness tail (Both inRest built) =>
              match decodedFit mask address tail inRest (omega) with
                | Both length fit => rewrite <- built in Both (omega) (rewrite fit in rfl)
    | [], [bit, ..address] => Void.exfalso (omega)
    | [maskBit, ..mask], [] => Void.exfalso (omega)

--| Every list of bits that fits the mask and the address is listed.
theorem fitDecoded ∀ (mask: List MaskBit) (address bits: List Bool) (sameAddress: address.length = mask.length)
    (sameBits: bits.length = mask.length) (fit: Spec.allFit mask address bits = True): bits ∈ decodeBits mask address :=
  match mask, address, bits with
    | [], [], [] => Inl rfl
    | [Off, ..mask], [bit, ..address], [chosen, ..bits] =>
      rewrite fit.left.read in
        List.memMap (decodeBits mask address) bits (fitDecoded mask address bits (omega) (omega) fit.right) (Cons bit)
    | [On, ..mask], [bit, ..address], [chosen, ..bits] =>
      rewrite fit.left in
        List.memMap (decodeBits mask address) bits (fitDecoded mask address bits (omega) (omega) fit.right) (Cons True)
    | [X, ..mask], [bit, ..address], [chosen, ..bits] =>
      let rest := decodeBits mask address
      let inRest := fitDecoded mask address bits (omega) (omega) fit.right
      match chosen with
        | False => List.memAppendLeft [False, ..bits] (rest.map (Cons False)) (rest.map (Cons True)) (List.memMap rest bits inRest (Cons False))
        | True => List.memAppendRight [True, ..bits] (rest.map (Cons False)) (rest.map (Cons True)) (List.memMap rest bits inRest (Cons True))
    | [], [], [chosen, ..bits] => Void.exfalso (omega)
    | [], [bit, ..address], bits => Void.exfalso (omega)
    | [maskBit, ..mask], [], bits => Void.exfalso (omega)
    | [maskBit, ..mask], [bit, ..address], [] => Void.exfalso (omega)

theorem decodeSound ∀ (mask: Mask) (address: Nat) (target: Nat) (member: target ∈ mask.decode address): Spec.Decodes mask address target = True :=
  let width := mask.bits.length
  match List.memMapElim Nat.fromBits target (decodeBits mask.bits (Nat.toBits width address)) member with
    | Witness bits (Both listed built) =>
      match decodedFit mask.bits (Nat.toBits width address) bits listed (Nat.toBitsLength width address) with
        | Both length fit =>
          let below: Nat.fromBits bits < Nat.pow 2 width := rewrite length at Nat.fromBitsBelow bits
          let back: Nat.toBits width (Nat.fromBits bits) = bits := rewrite length at Nat.toBitsFromBits bits
          rewrite <- built in
            match small: Nat.fromBits bits < Nat.pow 2 width with
              | True => rewrite back, fit in rfl

theorem decodeComplete ∀ (mask: Mask) (address: Nat) (target: Nat) (decodes: Spec.Decodes mask address target = True): target ∈ mask.decode address :=
  let width := mask.bits.length
  let below: target < Nat.pow 2 width := omega [decodes.left]
  let listed :=
    fitDecoded mask.bits (Nat.toBits width address) (Nat.toBits width target) (Nat.toBitsLength width address) (Nat.toBitsLength width target)
      decodes.right
  rewrite <- Nat.fromBitsToBits width target below in List.memMap _ (Nat.toBits width target) listed Nat.fromBits

--| The decoder's list holds an address exactly when the spec's write reaches it.
theorem decodeContains ∀ (mask: Mask) (address: Nat) (target: Nat): (mask.decode address).contains target = Spec.Decodes mask address target :=
  match decodes: Spec.Decodes mask address target with
    | True => (decodeComplete mask address target decodes)
    | False =>
      match contains: (mask.decode address).contains target with
        | True =>
          Void.exfalso
            (Bool.trueNotFalse (Eq.trans (Eq.sym (decodeSound mask address target contains.read)) decodes))
        | False => rfl
