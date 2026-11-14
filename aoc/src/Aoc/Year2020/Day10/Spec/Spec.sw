--| Day 10 as the puzzle states it, about the adapters' ratings: which chains
--| of adapters connect the outlet to the device, part 1's distribution of
--| differences over a chain of every adapter, and part 2's count of the
--| arrangements that connect. The proofs (Proofs/) show the program's
--| answers are these.

namespace Aoc.Year2020.Day10.Spec
import Std (Char, List, Parse)

--| A rating a line, in decimal.
def RatingWritten (read: List Char) (rating: Nat): Prop :=
  read ≠ [] ∧ read.all Parse.isDigit = True ∧ rating = Parse.digitsValue read

--| "Any given adapter can take an input 1, 2, or 3 jolts lower than its
--| rating."
def Takes (input rating: Nat): Bool := [1, 2, 3].contains (rating - input)

--| "Your device has a built-in joltage adapter rated for 3 jolts higher than
--| the highest-rated adapter in your bag": `highest` is that adapter's.
def Highest (adapters: List Nat) (highest: Nat): Prop := highest ∈ adapters ∧ (∀ (x: Nat) => x ∈ adapters → x ≤ highest)

--| From "the charging outlet near your seat as having an effective joltage
--| rating of 0" through `adapters` to the device, each takes the one before.
def Connects (adapters: List Nat) (device: Nat): Bool := [0, ..adapters, device].chain Takes

--| How many times, along `joltages`, the next is `difference` higher.
def differencesOf (joltages: List Nat) (difference: Nat): Nat :=
  joltages.zipWithNext.count (step => step.snd == step.fst + difference)

--| "If you use every adapter in your bag at once, what is the distribution
--| of joltage differences between the charging outlet, your adapters, and
--| your device? What is the number of 1-jolt differences multiplied by the
--| number of 3-jolt differences?": `chain` is the bag in some order that
--| connects.
def Part1 (adapters: List Nat) (answer: Nat): Prop :=
  ∃ (highest: Nat) => Highest adapters highest
    ∧ ∃ (chain: List Nat) => List.Perm chain adapters
      ∧ Connects chain (highest + 3) = True
      ∧ answer = differencesOf [0, ..chain, highest + 3] 1 * differencesOf [0, ..chain, highest + 3] 3

--| The ways of keeping some elements of a list, in order, and leaving out
--| the rest: each element is left out or kept.
def subsequences: (xs: List Nat) → List (List Nat)
  | [] => [[]]
  | [x, ..rest] => subsequences rest ++ (subsequences rest).map (kept => [x, ..kept])

--| "What is the total number of distinct ways you can arrange the adapters
--| to connect the charging outlet to your device?" An arrangement uses some
--| of the adapters, and only lowest first can each take the one before; so
--| the arrangements are the subsequences of the bag sorted by rating that
--| connect. (Two adapters with the same rating count as different ones; no
--| input has any.)
def Part2 (adapters: List Nat) (answer: Nat): Prop :=
  ∃ (highest: Nat) => Highest adapters highest
    ∧ answer = (subsequences adapters.sort).count (kept => Connects kept (highest + 3))
