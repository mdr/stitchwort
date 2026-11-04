--| Numbers in fixed-width fields: the spec's `bitsOf` and std's
--| `Nat.fromBits` undo each other, when the number fits.

namespace Aoc.Year2021.Day16.Proofs
import Aoc.Year2021.Day16.Spec (bitsOf)
import Std (Bool, Eq, List, Nat)

theorem lengthBitsOf: (width: Nat) → (n: Nat) → (bitsOf width n).length = width
  | 0, n => rfl
  | Succ width, n => rewrite List.lengthSnoc (bitsOf width (n / 2)) (n % 2 == 1), lengthBitsOf width (n / 2) in rfl

--| A bit after the others doubles their number and adds itself.
theorem fromBitsSnoc (bits: List Bool) (bit: Bool): Nat.fromBits (bits ++ [bit]) = Nat.fromBits bits * 2 + Bool.toNat bit :=
  rewrite List.foldLeftAppend bits 0 [bit] (acc bit => acc * 2 + Bool.toNat bit) in rfl

--| The last bit of a number is whether it is odd.
theorem parityBit (n: Nat): Bool.toNat (n % 2 == 1) = n % 2 :=
  let below := Nat.modLess n 2 (omega)
  match e: n % 2 with
    | 0 => rfl
    | 1 => rfl
    | Succ (Succ k) => omega

--| A number that fits in `width` bits is read back from them.
theorem fromBitsOf: (width: Nat) → (n: Nat) → n < Nat.pow 2 width → Nat.fromBits (bitsOf width n) = n
  | 0, n, small => omega
  | Succ width, n, small =>
    let split := Nat.divModEq n 2 (omega)
    let half := fromBitsOf width (n / 2) (omega [Nat.powSucc 2 width])
    rewrite fromBitsSnoc (bitsOf width (n / 2)) (n % 2 == 1), half, parityBit n in omega

--| Doubling a number and adding a bit: half of it is the number, and the
--| bit is whether it is odd.
theorem halfOfDouble (acc: Nat) (bit: Bool): (acc * 2 + Bool.toNat bit) / 2 = acc :=
  let split := Nat.divModEq (acc * 2 + Bool.toNat bit) 2 (omega)
  let below := Nat.modLess (acc * 2 + Bool.toNat bit) 2 (omega)
  match bit with
    | True => omega
    | False => omega

theorem parityOfDouble (acc: Nat) (bit: Bool): ((acc * 2 + Bool.toNat bit) % 2 == 1) = bit :=
  let split := Nat.divModEq (acc * 2 + Bool.toNat bit) 2 (omega)
  let below := Nat.modLess (acc * 2 + Bool.toNat bit) 2 (omega)
  match bit with
    | True =>
      let odd: (acc * 2 + 1) % 2 = 1 := omega
      rewrite odd in rfl
    | False =>
      let even: (acc * 2 + 0) % 2 = 0 := omega
      rewrite even in rfl

--| Reading bits after a number `acc`, then writing the result in as many
--| more bits, gives `acc`'s bits and then those bits.
theorem bitsOfFold (k: Nat): (acc: Nat) → (bits: List Bool) →
    bitsOf (k + bits.length) (List.foldLeft bits acc (acc bit => acc * 2 + Bool.toNat bit)) = bitsOf k acc ++ bits
  | acc, [] => rewrite Nat.addZero k, List.appendNil (bitsOf k acc) in rfl
  | acc, [bit, ..rest] =>
    let more := bitsOfFold (Succ k) (acc * 2 + Bool.toNat bit) rest
    let step: bitsOf (Succ k) (acc * 2 + Bool.toNat bit) ++ rest = bitsOf k acc ++ [bit, ..rest] :=
      rewrite parityOfDouble acc bit, halfOfDouble acc bit, List.appendAssoc (bitsOf k acc) [bit] rest in rfl
    Eq.trans more step

--| Any bits are the number they read as, written in as many bits.
theorem bitsOfFromBits (bits: List Bool): bitsOf bits.length (Nat.fromBits bits) = bits := bitsOfFold 0 0 bits

--| The number bits read as fits in them.
theorem fromBitsBelow (bits: List Bool): Nat.fromBits bits < Nat.pow 2 bits.length := omega [Nat.fromBitsFlipped bits]
