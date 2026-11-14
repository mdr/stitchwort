--| Day 9 as the puzzle states it, about the list of numbers received: which
--| number is the first invalid one, and what an encryption weakness is. The
--| proofs (Proofs/) show the program's answers are these.

namespace Aoc.Year2020.Day09.Spec
import Std (Char, List, Parse)

--| A number a line, in decimal.
def NumberWritten (read: List Char) (number: Nat): Prop :=
  read ≠ [] ∧ read.all Parse.isDigit = True ∧ number = Parse.digitsValue read

--| "Each number you receive should be the sum of any two of the 25
--| immediately previous numbers. The two numbers will have different
--| values."
def SumOfTwo (previous: List Nat) (number: Nat): Prop :=
  ∃ (a: Nat) => ∃ (b: Nat) => a ∈ previous ∧ b ∈ previous ∧ a ≠ b ∧ a + b = number

--| "The 25 immediately previous numbers", for a preamble of 25: the
--| `preamble` numbers before the one at `position` (counting the first as
--| 0), for a position after the preamble.
def previous (numbers: List Nat) (preamble position: Nat): List Nat :=
  numbers.drop (position - preamble) |> .take preamble

--| "Find the first number in the list (after the preamble) which is not the
--| sum of two of the 25 numbers before it": `answer` is at `position`, after
--| the preamble, and isn't such a sum, and every number between the
--| preamble and it is.
def Part1 (numbers: List Nat) (preamble answer: Nat): Prop :=
  ∃ (position: Nat) => preamble ≤ position
    ∧ numbers.get position = Some answer
    ∧ ¬SumOfTwo (previous numbers preamble position) answer
    ∧ (∀ (earlier: Nat) => preamble ≤ earlier < position
      → ∀ (number: Nat) => numbers.get earlier = Some number → SumOfTwo (previous numbers preamble earlier) number)

--| "A contiguous set of ... numbers in your list": the numbers from `start`
--| on, `length` of them (fewer where the list ends first).
def Contiguous (numbers run: List Nat): Prop :=
  ∃ (start: Nat) => ∃ (length: Nat) => run = (numbers.drop start |> .take length)

--| "Find a contiguous set of at least two numbers in your list which sum to
--| the invalid number from step 1", then "add together the smallest and
--| largest number in this contiguous range".
def Weakness (numbers: List Nat) (invalid answer: Nat): Prop :=
  ∃ (run: List Nat) => Contiguous numbers run
    ∧ 2 ≤ run.length
    ∧ run.sum = invalid
    ∧ ∃ (smallest: Nat) => ∃ (largest: Nat) => smallest ∈ run
      ∧ largest ∈ run
      ∧ (∀ (x: Nat) => x ∈ run → smallest ≤ x ≤ largest)
      ∧ answer = smallest + largest

--| "What is the encryption weakness in your XMAS-encrypted list of
--| numbers?": the weakness for part 1's invalid number.
def Part2 (numbers: List Nat) (preamble answer: Nat): Prop :=
  ∃ (invalid: Nat) => Part1 numbers preamble invalid ∧ Weakness numbers invalid answer
