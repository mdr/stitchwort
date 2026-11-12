--| The parser keeps the promise the answers' theorems need: in a
--| successful parse no two rules are for the same pair. With it, the
--| answers are the puzzle's for every input that parses.
-- (D2108)

namespace Aoc.Year2021.Day14.Proofs
import Aoc.Year2021.Day14 (..)
import Aoc.Year2021.Day14.Spec (..)
import Std (Bool, DecEq, Eq, Fail, List, Option, Result, Void)

--| If no pair is listed again further on, the pairs are distinct.
theorem firstRepeatedNone (pairs: List ElementPair) (none: firstRepeated pairs = None): List.Distinct pairs :=
  match pairs with
    | [] => ()
    | [pair, ..rest] =>
      match c: List.contains rest pair with
        | False =>
          let fresh := (member: pair ∈ rest) =>
            Bool.trueNotFalse (Eq.trans (Eq.sym (List.anyOfMem rest (other => other == pair) pair (DecEq.refl pair) member)) c)
          Both fresh (firstRepeatedNone rest none)

--| `checkManual` gives the manual back, and only if no pair has two rules...
theorem checkManualOk (manual: Manual) (result: Manual) (h: Fail.toResult (() => checkManual manual) = Ok result):
    result = manual ∧ firstRepeated (manual.rules.map Rule.pair) = None :=
  match e: firstRepeated (manual.rules.map Rule.pair) with
    | None => Both (Eq.sym (Result.okInjective h)) rfl

--| ...whatever reads it.
theorem parsedNoRepeat (read: () → {Fail} Manual) (manual: Manual) (parsed: Fail.toResult (() => checkManual (read ())) = Ok manual):
    firstRepeated (manual.rules.map Rule.pair) = None :=
  let split := rewrite Fail.toResultThen read checkManual at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkManual x)) manual split
    (found _ checked =>
      let (Both same none) := checkManualOk found manual checked
      rewrite same in none)

--| If `parseManual` reads `input` as `manual`, no two of its rules are for
--| the same pair.
theorem parseOneRulePerPair (input: Text) (manual: Manual) (parsed: Fail.toResult (() => parseManual input) = Ok manual): OneRulePerPair manual.rules :=
  firstRepeatedNone (manual.rules.map Rule.pair) (parsedNoRepeat _ manual parsed)

--| The answers from the input, with no hypothesis but the successful parse.
theorem part1FromInput (input: Text) (manual: Manual) (parsed: Fail.toResult (() => parseManual input) = Ok manual): solvePart1 manual = answer 10 manual :=
  part1Correct manual (parseOneRulePerPair input manual parsed)

theorem part2FromInput (input: Text) (manual: Manual) (parsed: Fail.toResult (() => parseManual input) = Ok manual): solvePart2 manual = answer 40 manual :=
  part2Correct manual (parseOneRulePerPair input manual parsed)
