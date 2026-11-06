--| Day 18 proved, about the input text: for every input the parser reads,
--| each line is the expression the parser gave for it, written out with a
--| shape the part's rules allow (Parse.sw), and the program's answer is the
--| sum of those expressions' values, so it is an answer the spec allows.
--| Not proved: that the rules allow only one expression for a line, so
--| not that the answer is the only one.

namespace Aoc.Year2020.Day18.Proofs
import Aoc.Year2020.Day18 (..)
import Aoc.Year2020.Day18 (Spec)
import Std (Eq, Fail, List, Nat, Parse, Result, Text)

theorem valueSpec: (expression: Expression) → expression.value = Spec.value expression
  | Number value => rfl
  | Operation Plus left right => rewrite valueSpec left, valueSpec right in rfl
  | Operation Times left right => rewrite valueSpec left, valueSpec right in rfl
  | Parenthesised inner => valueSpec inner

theorem sumSpec (homework: Homework): homework.sum = (homework.expressions.map Spec.value).sum :=
  rewrite List.mapCong homework.expressions Expression.value Spec.value valueSpec in rfl

--| If `parseHomework` reads `input`, each line is its expression, under
--| the rules `strengthOf` that `precedence`'s levels rank.
theorem parseMeans (input: Text) (precedence: Precedence) (strengthOf: Operator → Nat) (ranked: Ranked strengthOf 0 precedence.levels)
    (homework: Homework) (parsed: Fail.toResult (() => parseHomework input precedence) = Ok homework):
    List.All2 (Spec.Means strengthOf) (input.lines.map Text.toList) homework.expressions :=
  let split := rewrite Fail.toResultThen (() => Parse.eachLine input (() => precedence.expression)) (expressions => ({ expressions }: Homework)) at parsed
  Result.flatMapEqOk _ (expressions => Fail.toResult (() => ({ expressions }: Homework))) homework split (expressions read made =>
    rewrite <- Result.okInjective made in
      Parse.eachLineReads input (() => precedence.expression) (Spec.Means strengthOf) expressions read (readsExpression strengthOf precedence ranked))

theorem answerCorrect (input: Text) (precedence: Precedence) (strengthOf: Operator → Nat) (ranked: Ranked strengthOf 0 precedence.levels)
    (homework: Homework) (parsed: Fail.toResult (() => parseHomework input precedence) = Ok homework):
    Spec.Answer strengthOf input homework.sum :=
  Witness homework.expressions (Both (parseMeans input precedence strengthOf ranked homework parsed) (sumSpec homework))

theorem samePrecedenceRanked: Ranked Spec.part1Strength 0 samePrecedence.levels := Both (Both rfl (Both rfl Trivial)) Trivial

theorem additionFirstRanked: Ranked Spec.part2Strength 0 additionFirst.levels := Both (Both rfl Trivial) (Both (Both rfl Trivial) Trivial)

--| Part 1: for every input the parser reads with the same precedence for
--| `+` and `*`, its sum is an answer the spec allows.
theorem part1Correct (input: Text) (homework: Homework) (parsed: Fail.toResult (() => parseHomework input samePrecedence) = Ok homework):
    Spec.Part1 input homework.sum :=
  answerCorrect input samePrecedence Spec.part1Strength samePrecedenceRanked homework parsed

--| Part 2: the same, with `+` before `*`.
theorem part2Correct (input: Text) (homework: Homework) (parsed: Fail.toResult (() => parseHomework input additionFirst) = Ok homework):
    Spec.Part2 input homework.sum :=
  answerCorrect input additionFirst Spec.part2Strength additionFirstRanked homework parsed
