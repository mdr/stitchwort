--| Day 9 proved, about the input text: for every input the parser reads,
--| its lines are the numbers written in decimal (Parse.sw); part 1 is the
--| first number after the preamble that isn't the sum of two different
--| numbers among the `preamble` before it (Window.sw, Part1.sw); and part 2
--| is the smallest plus the largest number of a contiguous run of at least
--| two numbers summing to part 1's (Part2.sw). Both answer whenever the
--| puzzle has an answer, and part 1's is the only one (Part1.sw,
--| Complete.sw). For any preamble: the puzzle uses 25, its example 5.

namespace Aoc.Year2020.Day09.Proofs
import Aoc.Year2020.Day09 (..)
import Aoc.Year2020.Day09 (Spec)
import Std (Fail, Iff, List, Option, Result, Text)

theorem part1Correct ∀ (input: Text) (data: XmasData) (parsed: Fail.toResult (() => parseData input) = Ok data) (preamble: Nat) (answer: Nat)
    (solved: data.firstInvalid preamble = Some answer):
    List.All2 Spec.NumberWritten (input.lines.map Text.toList) data.numbers ∧ Spec.Part1 data.numbers preamble answer :=
  Both (parseWritten input data parsed) (part1Rules data preamble answer solved)

theorem part2Correct ∀ (input: Text) (data: XmasData) (parsed: Fail.toResult (() => parseData input) = Ok data) (preamble: Nat) (invalid: Nat)
    (answer: Nat) (first: data.firstInvalid preamble = Some invalid) (solved: data.weakness invalid = Some answer):
    List.All2 Spec.NumberWritten (input.lines.map Text.toList) data.numbers ∧ Spec.Part2 data.numbers preamble answer :=
  Both (parseWritten input data parsed) (Witness invalid (Both (part1Rules data preamble invalid first) (weaknessRules data invalid answer solved)))

--| Part 1 answers exactly when the puzzle has a first invalid number, and
--| then with it.
theorem part1Exactly ∀ (data: XmasData) (preamble: Nat) (answer: Nat): data.firstInvalid preamble = Some answer ↔ Spec.Part1 data.numbers preamble answer :=
  { forward = found => part1Rules data preamble answer found, backward = first => part1Complete data preamble answer first }

--| Part 2 answers whenever the puzzle has an answer. Two runs could have
--| different weaknesses; the puzzle expects one.
theorem part2Complete ∀ (data: XmasData) (preamble: Nat) (answer: Nat) (has: Spec.Part2 data.numbers preamble answer):
    (data.firstInvalid preamble).flatMap data.weakness ≠ None :=
  let (Witness invalid (Both first weak)) := has
  rewrite part1Complete data preamble invalid first in weaknessComplete data invalid answer weak
