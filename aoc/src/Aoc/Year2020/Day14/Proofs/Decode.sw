--| Part 2's decoder lists exactly the spec's addresses: an address is in
--| `mask.decode address` if and only if `Spec.Decodes` says the write
--| reaches it. Bit lists first (`decodeBits` against `Spec.allFit`), then
--| numbers through `Nat.fromBits` and `Nat.toBits`.

namespace Aoc.Year2020.Day14.Proofs
import Aoc.Year2020.Day14 (..)
import Aoc.Year2020.Day14 (Spec)
import Std (Bool, DecEq, Eq, List, Nat, Void)

--| What `decodeBits` lists fits the mask and the address, bit by bit.
theorem decodedFit: ∀ (mask: List MaskBit) (address bits: List Bool) => bits ∈ decodeBits mask address →
    address.length = mask.length → bits.length = mask.length ∧ Spec.allFit mask address bits = True
  | [], [], bits, member, same =>
    match member with
      | Inl isNil => rewrite <- isNil in Both rfl rfl
      | Inr none => Void.exfalso none
  | [Off, ..mask], [bit, ..address], bits, member, same =>
    match List.memMapElim (Cons bit) bits (decodeBits mask address) member with
      | Witness rest (Both inRest built) =>
        match decodedFit mask address rest inRest (omega) with
          | Both length fit => rewrite <- built in Both (omega) (rewrite fit, DecEq.refl bit in rfl)
  | [On, ..mask], [bit, ..address], bits, member, same =>
    match List.memMapElim (Cons True) bits (decodeBits mask address) member with
      | Witness rest (Both inRest built) =>
        match decodedFit mask address rest inRest (omega) with
          | Both length fit => rewrite <- built in Both (omega) (rewrite fit in rfl)
  | [X, ..mask], [bit, ..address], bits, member, same =>
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
  | [], [bit, ..address], bits, member, same => Void.exfalso (omega)
  | [maskBit, ..mask], [], bits, member, same => Void.exfalso (omega)

--| Every list of bits that fits the mask and the address is listed.
theorem fitDecoded: ∀ (mask: List MaskBit) (address bits: List Bool) => address.length = mask.length →
    bits.length = mask.length → Spec.allFit mask address bits = True → bits ∈ decodeBits mask address
  | [], [], [], sameAddress, sameBits, fit => Inl rfl
  | [Off, ..mask], [bit, ..address], [chosen, ..bits], sameAddress, sameBits, fit =>
    rewrite DecEq.sound (Bool.andLeft fit) in
      List.memMap (decodeBits mask address) bits (fitDecoded mask address bits (omega) (omega) (Bool.andRight fit)) (Cons bit)
  | [On, ..mask], [bit, ..address], [chosen, ..bits], sameAddress, sameBits, fit =>
    rewrite Bool.andLeft fit in
      List.memMap (decodeBits mask address) bits (fitDecoded mask address bits (omega) (omega) (Bool.andRight fit)) (Cons True)
  | [X, ..mask], [bit, ..address], [chosen, ..bits], sameAddress, sameBits, fit =>
    let rest := decodeBits mask address
    let inRest := fitDecoded mask address bits (omega) (omega) (Bool.andRight fit)
    match chosen with
      | False => List.memAppendLeft [False, ..bits] (rest.map (Cons False)) (rest.map (Cons True)) (List.memMap rest bits inRest (Cons False))
      | True => List.memAppendRight [True, ..bits] (rest.map (Cons False)) (rest.map (Cons True)) (List.memMap rest bits inRest (Cons True))
  | [], [], [chosen, ..bits], sameAddress, sameBits, fit => Void.exfalso (omega)
  | [], [bit, ..address], bits, sameAddress, sameBits, fit => Void.exfalso (omega)
  | [maskBit, ..mask], [], bits, sameAddress, sameBits, fit => Void.exfalso (omega)
  | [maskBit, ..mask], [bit, ..address], [], sameAddress, sameBits, fit => Void.exfalso (omega)

theorem decodeSound (mask: Mask) (address: Nat) (target: Nat) (member: target ∈ mask.decode address): Spec.Decodes mask address target = True :=
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
              | False => Void.exfalso (omega)

theorem decodeComplete (mask: Mask) (address: Nat) (target: Nat) (decodes: Spec.Decodes mask address target = True): target ∈ mask.decode address :=
  let width := mask.bits.length
  let below: target < Nat.pow 2 width := omega [Bool.andLeft decodes]
  let listed :=
    fitDecoded mask.bits (Nat.toBits width address) (Nat.toBits width target) (Nat.toBitsLength width address) (Nat.toBitsLength width target)
      (Bool.andRight decodes)
  rewrite <- Nat.fromBitsToBits width target below in List.memMap _ (Nat.toBits width target) listed Nat.fromBits

--| The decoder's list holds an address exactly when the spec's write reaches it.
theorem decodeContains (mask: Mask) (address: Nat) (target: Nat): (mask.decode address).contains target = Spec.Decodes mask address target :=
  match decodes: Spec.Decodes mask address target with
    | True => (List.memContains (mask.decode address) target).backward (decodeComplete mask address target decodes)
    | False =>
      match contains: (mask.decode address).contains target with
        | True =>
          Void.exfalso
            (Bool.trueNotFalse (Eq.trans (Eq.sym (decodeSound mask address target ((List.memContains (mask.decode address) target).forward contains))) decodes))
        | False => rfl
