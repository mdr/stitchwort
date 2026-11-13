--| Day 10 proved, about the input text: for every input the parser reads,
--| its lines are the ratings written in decimal (Parse.sw); part 1's answer
--| is the distribution of differences along a chain of every adapter that
--| connects the outlet to the device, exactly when there is one (Part1.sw);
--| and part 2's is the number of subsequences of the sorted bag that
--| connect (Part2.sw). Both answer exactly when the bag isn't empty and
--| (part 1) its adapters chain, and part 1's answer is the only one.

namespace Aoc.Year2020.Day10.Proofs
import Aoc.Year2020.Day10 (..)
import Aoc.Year2020.Day10 (Spec)
import Std (Eq, Fail, List, Option, Result, Text)

theorem part1Correct ∀ (input: Text) (bag: Bag) (parsed: Fail.toResult (() => parseBag input) = Ok bag) (answer: Nat)
    (solved: bag.distribution = Some answer):
    List.All2 Spec.RatingWritten (input.lines.map Text.toList) bag.adapters ∧ Spec.Part1 bag.adapters answer :=
  Both (parseWritten input bag parsed) (part1Rules bag answer solved)

theorem part2Correct ∀ (input: Text) (bag: Bag) (parsed: Fail.toResult (() => parseBag input) = Ok bag) (answer: Nat)
    (solved: bag.arrangements = Some answer):
    List.All2 Spec.RatingWritten (input.lines.map Text.toList) bag.adapters ∧ Spec.Part2 bag.adapters answer :=
  Both (parseWritten input bag parsed) (part2Rules bag answer solved)

--| Part 1 answers exactly when the spec has an answer, and then with it.
theorem part1Exactly ∀ (bag: Bag) (answer: Nat): bag.distribution = Some answer ↔ Spec.Part1 bag.adapters answer :=
  { forward = found => part1Rules bag answer found, backward = spec => part1Complete bag answer spec }

--| Part 2 likewise.
theorem part2Exactly ∀ (bag: Bag) (answer: Nat): bag.arrangements = Some answer ↔ Spec.Part2 bag.adapters answer :=
  { forward = found => part2Rules bag answer found, backward = spec => part2Complete bag answer spec }

--| "The" distribution names one number: any two answers the spec allows
--| are the same.
theorem part1Unique ∀ (bag: Bag) (one: Nat) (other: Nat) (first: Spec.Part1 bag.adapters one) (second: Spec.Part1 bag.adapters other): one = other :=
  Option.someInjective (Eq.trans (Eq.sym (part1Complete bag one first)) (part1Complete bag other second))
