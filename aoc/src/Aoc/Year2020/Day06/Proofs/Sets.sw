--| What a group's sets hold: `anyone` the letters some line has, `everyone`
--| the questions every line has.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Aoc.Year2020.Day06 (Spec)
import Std (Bool, Char, Eq, List, Set, Void, byDecision)

--| The people's answer sets, asked about a question, say what their lines say.
theorem anyAnswers: (lines: List (List Char)) → (people: List Person) → List.All2 PersonWritten lines people → (question: Char) →
    (people.map .answers).any (answers => answers.contains question) = lines.any (line => line.contains question)
  | [], [], all, question => rfl
  | [line, ..lines], [person, ..people], Both (Both nonEmpty (Both questions same)) rest, question =>
    rewrite same question, anyAnswers lines people rest question in rfl
  | [], [_, .._], impossible, question => Void.exfalso impossible
  | [_, .._], [], impossible, question => Void.exfalso impossible

theorem allAnswers: (lines: List (List Char)) → (people: List Person) → List.All2 PersonWritten lines people → (question: Char) →
    (people.map .answers).all (answers => answers.contains question) = lines.all (line => line.contains question)
  | [], [], all, question => rfl
  | [line, ..lines], [person, ..people], Both (Both nonEmpty (Both questions same)) rest, question =>
    rewrite same question, allAnswers lines people rest question in rfl
  | [], [_, .._], impossible, question => Void.exfalso impossible
  | [_, .._], [], impossible, question => Void.exfalso impossible

--| Everyone's answers folded in by intersection hold what the accumulator
--| holds and every line has.
theorem intersectContains (lines: List (List Char)) (people: List Person) (written: List.All2 PersonWritten lines people) (acc: Set Char) (question: Char):
    (List.foldLeft people acc (common person => common.intersect person.answers)).contains question = (acc.contains question ∧ lines.all (line => line.contains question)) :=
  rewrite <- allAnswers lines people written question in
    Eq.trans (Eq.cong (set => set.contains question) (Eq.sym (List.foldLeftMap people acc Set.intersect .answers)))
      (Set.containsFoldIntersect question (people.map .answers) acc)

--| Whatever some line has is a question.
theorem anyQuestion: (lines: List (List Char)) → (people: List Person) → List.All2 PersonWritten lines people → (question: Char) →
    lines.any (line => line.contains question) = True → Spec.questions.contains question = True
  | [], [], all, question, found => Void.exfalso (Bool.falseNotTrue found)
  | [line, ..lines], [person, ..people], Both (Both nonEmpty (Both questions same)) rest, question, found =>
    Bool.orElim (line.contains question) (lines.any (line => line.contains question)) _ found
      (inLine =>
        List.allMember isQuestion line questions question ((List.memContains line question).forward inLine))
      (inRest => anyQuestion lines people rest question inRest)
  | [], [_, .._], impossible, question, found => Void.exfalso impossible
  | [_, .._], [], impossible, question, found => Void.exfalso impossible

theorem questionsDistinct: List.Distinct Spec.questions := byDecision
