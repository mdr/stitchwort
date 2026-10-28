-- General facts the proofs use: bits of small numbers, and `List.all` on
-- a member.

namespace Aoc.Year2024.Day24.Proofs
import Std (Bool, List, Nat)

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
