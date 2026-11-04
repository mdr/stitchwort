--| What a group's sets hold: `anyone` the letters some line has, `everyone`
--| the questions every line has; and a set of questions has as many
--| members as the questions it holds.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Aoc.Year2020.Day06 (Spec)
import Std (Bool, Char, Eq, List, Map, Nat, Set, Void, byDecision)

theorem andAssoc: (a: Bool) → (b: Bool) → (c: Bool) → ((a ∧ b) ∧ c) = (a ∧ (b ∧ c))
  | True, b, c => rfl
  | False, b, c => rfl

--| Folding in the people's answers by union holds what the accumulator
--| holds, or what some line has.
theorem unionContains: (lines: List (List Char)) → (people: List Person) → List.All2 PersonWritten lines people → (acc: Set Char) → (question: Char) →
    (List.foldLeft (people.map (.answers)) acc Set.union).contains question = (acc.contains question ∨ lines.any (line => line.contains question))
  | [], [], all, acc, question => Eq.sym (Bool.orFalse (acc.contains question))
  | [line, ..lines], [person, ..people], Both (Both nonEmpty (Both questions same)) rest, acc, question =>
    rewrite unionContains lines people rest (Set.union acc person.answers) question, Set.containsUnion acc question person.answers, same question in
      Bool.orAssoc (acc.contains question) (line.contains question) (lines.any (line => line.contains question))
  | [], [_, .._], impossible, acc, question => Void.exfalso impossible
  | [_, .._], [], impossible, acc, question => Void.exfalso impossible

theorem intersectContains: (lines: List (List Char)) → (people: List Person) → List.All2 PersonWritten lines people → (acc: Set Char) → (question: Char) →
    (List.foldLeft people acc (common person => common.intersect person.answers)).contains question = (acc.contains question ∧ lines.all (line => line.contains question))
  | [], [], all, acc, question => Eq.sym (Bool.andTrue (acc.contains question))
  | [line, ..lines], [person, ..people], Both (Both nonEmpty (Both questions same)) rest, acc, question =>
    rewrite intersectContains lines people rest (Set.intersect acc person.answers) question, Set.containsIntersect acc question person.answers, same question in
      andAssoc (acc.contains question) (line.contains question) (lines.all (line => line.contains question))
  | [], [_, .._], impossible, acc, question => Void.exfalso impossible
  | [_, .._], [], impossible, acc, question => Void.exfalso impossible

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

--| A set holding only questions has as many members as there are questions
--| it holds.
theorem sizeCount (set: Set Char) (yes: Char → Bool) (inside: (question: Char) → set.contains question = True → Spec.questions.contains question = True)
    (agree: (question: Char) → Spec.questions.contains question = True → set.contains question = yes question): set.size = (Spec.questions.filter yes).length :=
  let same: List.Perm set.toList (Spec.questions.filter yes) :=
    List.permOfSameMembers set.toList (Spec.questions.filter yes) (Map.keysDistinct set.items) (List.distinctFilter Spec.questions yes questionsDistinct)
      (question member =>
        let found := (Set.memToList set question).forward member
        let isQuestion := inside question found
        List.memFilterIntro Spec.questions yes question ((List.memContains Spec.questions question).forward isQuestion) (rewrite <- agree question isQuestion in found))
      (question member =>
        match List.memFilter Spec.questions yes question member with
          | Both there held => (Set.memToList set question).backward (rewrite agree question ((List.memContains Spec.questions question).backward there) in held))
  Eq.trans (Set.sizeToList set) (List.permLength set.toList (Spec.questions.filter yes) same)
