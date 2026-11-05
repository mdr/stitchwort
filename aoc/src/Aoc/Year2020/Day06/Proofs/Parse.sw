--| The parser reads exactly the puzzle's format: a group is a person's line
--| each, the letters `a` to `z` of the questions they answered "yes" to, and
--| groups are separated by a blank line. If it reads `input`, the input is
--| the groups written out, and each person's set of answers has exactly
--| their line's letters.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Std (Bool, Char, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Set, Text)

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
    (Parse.readsMany1 _ _ (Parse.readsSatisfy _ _)) (lettersRead letters each =>
      match eachLetters lettersRead letters.toList each with
        | Both same questions =>
          Parse.readsDone ({ answers = Set.fromList letters.toList }: Person) _
            (rewrite List.appendNil lettersRead, same in
              Both (NonEmptyList.toListNotNil letters) (Both questions (question => containsFromList letters.toList question))))

--| `Parse.SepBy` for values kept in a `List`: they are a `NonEmptyList`'s elements.
def SepByList (spec: List Char → a → Prop) (separator: List Char → () → Prop) (read: List Char) (values: List a): Prop :=
  ∃ (listed: NonEmptyList a) => Parse.SepBy spec separator read listed ∧ values = listed.toList

--| A group: its people's lines, line breaks between.
def GroupWritten (read: List Char) (group: Group): Prop := SepByList PersonWritten (read u => Parse.LineBreak read) read group.people

theorem readsGroup: Parse.Reads group GroupWritten :=
  Parse.readsThen _ _ _ _ (Parse.readsLines person _ readsPerson) (peopleRead people written =>
    Parse.readsDone { people = people.toList } _ (rewrite List.appendNil peopleRead in Witness people (Both written rfl)))

--| If `parseGroups` reads `input`, the input is the groups written out, a
--| blank line between each two, then any line breaks.
theorem parseWritten (input: Text) (groups: List Group) (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ SepByList GroupWritten (read u => Parse.BlankLine read) read groups
        ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  Parse.allReads input (() => Parse.sections group |> .toList) _ groups parsed
    (Parse.readsMap (() => Parse.sections group) NonEmptyList.toList _ (Parse.readsSections group _ readsGroup))

--| A group's lines as the spec has them: each line is what was read.
def LinesWritten (read: List Char) (lines: List (List Char)): Prop := SepByList (line written => line = written) (read u => Parse.LineBreak read) read lines

--| What a repetition of separator and part read, with each part's value
--| replaced by another that relates to it.
theorem eachMap (spec: List Char → a → Prop) (other: List Char → c → Prop) (related: c → a → Prop) (separator: List Char → () → Prop)
    (step: (read: List Char) → (value: a) → spec read value → ∃ (other_: c) => other read other_ ∧ related other_ value):
    (read: List Char) → (values: List a) → Parse.Each (Parse.Then separator (u => spec)) read values →
      ∃ (others: List c) => Parse.Each (Parse.Then separator (u => other)) read others ∧ List.All2 related others values
  | read, [], each => Witness [] (Both each ())
  | read, [value, ..values], Witness first (Witness rest (Both split (Both (Witness separatorRead (Witness partRead (Witness u (Both joined (Both separated written))))) more))) =>
    match step partRead value written with
      | Witness z (Both zRead zRelated) =>
        match eachMap spec other related separator step rest values more with
          | Witness zs (Both zsRead zsRelated) =>
            Witness [z, ..zs]
              (Both (Witness first (Witness rest (Both split (Both (Witness separatorRead (Witness partRead (Witness u (Both joined (Both separated zRead))))) zsRead))))
                (Both zRelated zsRelated))

theorem sepByMap (spec: List Char → a → Prop) (other: List Char → c → Prop) (related: c → a → Prop) (separator: List Char → () → Prop)
    (step: (read: List Char) → (value: a) → spec read value → ∃ (other_: c) => other read other_ ∧ related other_ value)
    (read: List Char) (values: List a) (written: SepByList spec separator read values):
    ∃ (others: List c) => SepByList other separator read others ∧ List.All2 related others values :=
  match written with
    | Witness listed (Both (Witness firstRead (Witness afterRead (Witness head (Both split (Both firstWritten (Both isFirst each)))))) same) =>
      match step firstRead listed.head (rewrite isFirst at firstWritten in firstWritten) with
        | Witness z (Both zRead zRelated) =>
          match eachMap spec other related separator step afterRead listed.tail each with
            | Witness zs (Both zsRead zsRelated) =>
              Witness [z, ..zs]
                (Both (Witness ({ head = z, tail = zs }: NonEmptyList c)
                    (Both (Witness firstRead (Witness afterRead (Witness z (Both split (Both zRead (Both rfl zsRead)))))) rfl))
                  (rewrite same in Both zRelated zsRelated))
