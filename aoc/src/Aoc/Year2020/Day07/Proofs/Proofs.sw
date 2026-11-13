--| Day 7 proved, about the input text: for every input the parser reads,
--| its lines are the rules written out (Parse.sw), part 1 is the number of
--| colours those rules let eventually contain a shiny gold bag (Part1.sw),
--| and part 2, when it gives an answer, is the number of bags they require
--| inside one (Part2.sw). Part 2 gives no answer only where the rules go round
--| in a cycle, no depth settling it (Depth.sw).

namespace Aoc.Year2020.Day07.Proofs
import Aoc.Year2020.Day07 (..)
import Aoc.Year2020.Day07 (Spec)
import Std (Fail, List, Result, Text)

theorem part1Correct ∀ (input: Text) (rules: Rules) (parsed: Fail.toResult (() => parseRules input) = Ok rules):
    List.All2 Spec.RuleWritten (input.lines.map Text.toList) rules.all ∧ Spec.Part1 rules.all (solvePart1 rules) :=
  Both (parseWritten input rules parsed) (part1Rules rules)

theorem part2Correct ∀ (input: Text) (rules: Rules) (parsed: Fail.toResult (() => parseRules input) = Ok rules) (total: Nat)
    (solved: Fail.toResult (() => solvePart2 rules) = Ok total):
    List.All2 Spec.RuleWritten (input.lines.map Text.toList) rules.all ∧ Spec.Part2 rules.all total :=
  Both (parseWritten input rules parsed) (part2Rules rules total solved)

theorem part2Answers ∀ (rules: Rules) (total: Nat): Fail.toResult (() => solvePart2 rules) = Ok total ↔ Spec.Part2 rules.all total := {
  forward = solved => part2Rules rules total solved,
  backward = settled => part2Complete rules total settled
}
