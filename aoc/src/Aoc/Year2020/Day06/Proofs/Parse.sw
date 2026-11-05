--| The parser reads exactly the puzzle's format: a group is a person's line
--| each, the letters `a` to `z` of the questions they answered "yes" to, and
--| groups are separated by a blank line. If it reads `input`, the input is
--| the groups written out, and each person's set of answers has exactly
--| their line's letters.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Std (Bool, Char, Eq, Exists, Fail, List, Parse, Result, Set, Text)

--| A person's line: at least one letter, all questions, and the person's
--| answers hold those letters and no others.
def PersonWritten (read: List Char) (person: Person): Prop :=
  read ≠ [] ∧ read.all isQuestion = True ∧ ((question: Char) → person.answers.contains question = read.contains question)

theorem eachLetters: (read: List Char) → (letters: List Char) → Parse.Each (letter char => letter = [char] ∧ isQuestion char = True) read letters →
    read = letters ∧ letters.all isQuestion = True
  | read, [], each => Both each rfl
  | read, [letter, ..rest], Witness first (Witness after (Both split (Both (Both one question) more))) =>
    match eachLetters after rest more with
      | Both same questions => Both (rewrite split, one, same in rfl) (rewrite question, questions in rfl)

theorem containsFromList (letters: List Char) (question: Char): (Set.fromList letters).contains question = letters.contains question :=
  Bool.eqOf _ _
    (found => (List.memContains letters question).backward ((Set.containsFromListIff letters question).forward found))
    (found => (Set.containsFromListIff letters question).backward ((List.memContains letters question).forward found))

theorem readsPerson: Parse.Reads person PersonWritten :=
  Parse.readsThen _ _ _ _
    (Parse.readsMany1 _ _ (Parse.readsSatisfy _ _)) (lettersRead letters (Both each nonEmpty) =>
      match eachLetters lettersRead letters each with
        | Both same questions =>
          Parse.readsDone ({ answers = Set.fromList letters }: Person) _
            (rewrite List.appendNil lettersRead, same in
              Both (nonEmpty) (Both questions (question => containsFromList letters question))))

--| A group: its people's lines, line breaks between.
def GroupWritten (read: List Char) (group: Group): Prop := Parse.SepBy PersonWritten (read u => Parse.LineBreak read) read group.people

theorem readsGroup: Parse.Reads group GroupWritten :=
  Parse.readsThen _ _ _ _ (Parse.readsLines person _ readsPerson) (peopleRead people written =>
    Parse.readsDone { people } _ (rewrite List.appendNil peopleRead in written))

--| If `parseGroups` reads `input`, the input is the groups written out, a
--| blank line between each two, then any line breaks.
theorem parseWritten (input: Text) (groups: List Group) (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ Parse.SepBy GroupWritten (read u => Parse.BlankLine read) read groups
        ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  Parse.allReads input (() => Parse.sections group) _ groups parsed (Parse.readsSections group _ readsGroup)

--| The parts a separated list read, one per value.
theorem eachParts (spec: List Char → a → Prop) (separator: List Char → () → Prop): (read: List Char) → (values: List a) →
    Parse.Each (Parse.Then separator (u => spec)) read values → ∃ (parts: List (List Char)) => List.All2 spec parts values
  | read, [], each => Witness [] ()
  | read, [value, ..values], Witness first (Witness rest (Both split (Both (Witness separatorRead (Witness partRead (Witness u (Both joined (Both separated written))))) more))) =>
    match eachParts spec separator rest values more with
      | Witness parts allWritten => Witness [partRead, ..parts] (Both written allWritten)

theorem sepByParts (spec: List Char → a → Prop) (separator: List Char → () → Prop) (read: List Char) (values: List a) (written: Parse.SepBy spec separator read values):
    ∃ (parts: List (List Char)) => List.All2 spec parts values :=
  match written with
    | Witness first (Witness rest (Both same (Witness firstRead (Witness afterRead (Witness head (Both split (Both firstWritten (Both isFirst each)))))))) =>
      match eachParts spec separator afterRead rest each with
        | Witness parts allWritten => Witness [firstRead, ..parts] (rewrite same in Both (rewrite isFirst at firstWritten in firstWritten) allWritten)
