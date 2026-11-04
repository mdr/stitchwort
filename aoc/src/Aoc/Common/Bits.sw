--| A binary number, written as the puzzles do: the most significant bit
--| first, `True` for a 1. Its proofs are in `Aoc.Common.Proofs`
--| (Proofs/Bits.sw), which are `Nat.fromBits`'s and `Nat.toBits`'s lemmas
--| said of `Bits`.

namespace Aoc.Common
import Std (Bool, List, Nat, Option)

--| The bits of a number, the most significant first.
type Bits = { bits: List Bool }

--| The number the bits spell.
def Bits.value (number: Bits): Nat := Nat.fromBits number.bits

--| How many bits there are, leading zeros included.
def Bits.width (number: Bits): Nat := number.bits.length

--| The `width` bits of `n`, the most significant first (`n` mod 2^`width`).
def Bits.ofNat (width: Nat) (n: Nat): Bits := { bits = Nat.toBits width n }

--| Every bit flipped: with `width` bits, the number that adds to this one
--| to make 2^`width` - 1.
def Bits.complement (number: Bits): Bits := { bits = number.bits.map Bool.not }

--| The bit at `position`, counted from the left, from 0; none past the end.
def Bits.get (number: Bits) (position: Nat): Option Bool := number.bits.get position

--| No bits.
def Bits.empty: Bits := { bits = [] }

--| `number` with `bit` put in front of it as the new most significant bit.
def Bits.cons (number: Bits) (bit: Bool): Bits := { bits = [bit, ..number.bits] }

--| The first (most significant) bit; none if there are no bits.
def Bits.first (number: Bits): Option Bool := number.bits.head

--| The bits after the first, when the first is `bit`; none when it isn't or
--| there are no bits.
def Bits.afterBit (number: Bits) (bit: Bool): Option Bits :=
  match number.bits with
    | [] => None
    | [first, ..rest] => if first == bit then Some ({ bits = rest }) else None

--| `number` followed by `other`'s bits, as one number.
def Bits.append (number: Bits) (other: Bits): Bits := { bits = number.bits ++ other.bits }
