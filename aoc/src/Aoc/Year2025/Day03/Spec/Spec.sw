-- Day 3 as the puzzle states it: turn on exactly k of a bank's batteries, in the
-- bank's order. The headline theorem (Proofs/Best.sw) says the program's
-- `maxJoltage k bank` is the most joltage any such choice makes.

namespace Aoc.Year2025.Day03.Spec
import Aoc.Year2025.Day03 (Bank, Battery)
import Std (List, Nat)

-- `on` is k of the bank's batteries, turned on in the bank's order.
def TurnsOn (k: Nat) (bank: Bank) (on: List Battery): Prop :=
  on.Subsequence bank ∧ on.length = k
