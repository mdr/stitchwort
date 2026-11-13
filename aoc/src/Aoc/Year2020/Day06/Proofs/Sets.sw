--| What a group's sets hold: `anyone` the letters some line has, `everyone`
--| the questions every line has.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Aoc.Year2020.Day06 (Spec)
import Std (Bool, Char, Eq, List, NonEmptyList, Set, Void)

--| The people's answer sets, asked about a question, say what their lines say.
theorem anyAnswers: ∀ (lines: List (List Char)) (people: List Person) => List.All2 PersonWritten lines people → ∀ (question: Char) =>
    (people.map .answers).any (answers => answers.contains question) = lines.any (line => line.contains question)
  | [], [], all, question => rfl
  | [line, ..lines], [person, ..people], Both (Both nonEmpty (Both questions same)) rest, question =>
    rewrite same question, anyAnswers lines people rest question in rfl
  | [], [_, .._], impossible, question => Void.exfalso impossible
  | [_, .._], [], impossible, question => Void.exfalso impossible

theorem allAnswers: ∀ (lines: List (List Char)) (people: List Person) => List.All2 PersonWritten lines people → ∀ (question: Char) =>
    (people.map .answers).all (answers => answers.contains question) = lines.all (line => line.contains question)
  | [], [], all, question => rfl
  | [line, ..lines], [person, ..people], Both (Both nonEmpty (Both questions same)) rest, question =>
    rewrite same question, allAnswers lines people rest question in rfl
  | [], [_, .._], impossible, question => Void.exfalso impossible
  | [_, .._], [], impossible, question => Void.exfalso impossible

--| The intersection of everyone's answers holds what every line has.
theorem intersectContains (lines: List (List Char)) (people: NonEmptyList Person) (written: List.All2 PersonWritten lines people.toList) (question: Char):
    (people.map .answers).intersectAll.contains question = lines.all (line => line.contains question) :=
  Eq.trans (NonEmptyList.containsIntersectAll (people.map .answers) question) (allAnswers lines people.toList written question)

--| Whatever some line has is a question.
theorem anyQuestion: ∀ (lines: List (List Char)) (people: List Person) => List.All2 PersonWritten lines people → ∀ (question: Char) =>
    lines.any (line => line.contains question) = True → Spec.questions.contains question = True
  | [], [], all, question, found => cases
  | [line, ..lines], [person, ..people], Both (Both nonEmpty (Both questions same)) rest, question, found =>
    match found with
      | Inl inLine => questions.read question inLine.read
      | Inr inRest => anyQuestion lines people rest question inRest
  | [], [_, .._], impossible, question, found => Void.exfalso impossible
  | [_, .._], [], impossible, question, found => Void.exfalso impossible

theorem questionsDistinct: List.Distinct Spec.questions :=
  (List.isDistinctIff Spec.questions).forward rfl

--| Whatever every line has is a question: there is a first line, and it is all questions.
theorem everyQuestion: ∀ (lines: List (List Char)) (people: List Person) => List.All2 PersonWritten lines people → people ≠ [] → ∀ (question: Char) =>
    lines.all (line => line.contains question) = True → Spec.questions.contains question = True
  | [], [], all, some, question, found => Void.exfalso (some rfl)
  | [line, ..lines], [person, ..people], Both (Both nonEmpty (Both questions same)) rest, some, question, found =>
    let inLine: line.contains question = True := found.left
    questions.read question inLine.read
  | [], [_, .._], impossible, some, question, found => Void.exfalso impossible
  | [_, .._], [], impossible, some, question, found => Void.exfalso impossible
