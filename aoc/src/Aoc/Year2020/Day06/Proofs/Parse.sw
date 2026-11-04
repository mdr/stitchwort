--| The parser reads exactly the puzzle's format: groups separated by blank
--| lines, a person on each line of a group, each person's line the letters
--| `a` to `z` of the questions they answered "yes" to. If `parseGroups`
--| reads `input` as `groups`, the input is the groups written out, and
--| each person's set of answers has exactly the letters of their line.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Std (Bool, Char, Eq, Exists, Fail, List, Parse, Result, Set, Text)

--| What `sepBy1` read: `Parse.SepBy` without the `first` of its statement,
--| which `Parse.SepBy` leaves unrelated to the value the first read gave.
def SepBy (spec: List Char → a → Prop) (separator: List Char → () → Prop) (read: List Char) (values: List a): Prop :=
  ∃ (first: a) => ∃ (rest: List a) => ∃ (firstRead: List Char) => ∃ (restRead: List Char) =>
    values = [first, ..rest] ∧ read = firstRead ++ restRead ∧ spec firstRead first ∧ Parse.Each (Parse.Then separator (u => spec)) restRead rest

theorem readsSepBy1 (p: () → {Parse} a) (separator: () → {Parse} ()) (spec: List Char → a → Prop) (separatorSpec: List Char → () → Prop)
    (reads: Parse.Reads p spec) (readsSeparator: Parse.Reads separator separatorSpec): Parse.Reads (() => Parse.sepBy1 p separator) (SepBy spec separatorSpec) :=
  Parse.readsWeaken _ _ _
    (Parse.readsBind p
      (first =>
        Cons first (Parse.many (() =>
          separator()
          p())))
      spec (first read values => ∃ (rest: List a) => Parse.Each (Parse.Then separatorSpec (u => spec)) read rest ∧ values = Cons first rest) reads
      (first =>
        Parse.readsMap
          (() =>
            Parse.many (() =>
              separator()
              p()))
          (Cons first) _
          (Parse.readsMany _ _ (Parse.readsBind separator (u => p()) separatorSpec (u => spec) readsSeparator (u => reads)))))
    (read values h =>
      match h with
        | Witness firstRead (Witness restRead (Witness first (Both split (Both holds (Witness rest (Both each same)))))) =>
          Witness first (Witness rest (Witness firstRead (Witness restRead (Both same (Both split (Both holds each)))))))

theorem eachSeparated (spec: List Char → a → Prop) (separator: List Char → () → Prop):
    (read: List Char) → (values: List a) → Parse.Each (Parse.Then separator (u => spec)) read values → ∃ (reads: List (List Char)) => List.All2 spec reads values
  | read, [], each => Witness [] ()
  | read, [value, ..rest], Witness first (Witness after (Both split (Both (Witness separatorRead (Witness valueRead (Witness u (Both same (Both sep valid))))) more))) =>
    match eachSeparated spec separator after rest more with
      | Witness reads all => Witness [valueRead, ..reads] (Both valid all)

--| One read per value.
theorem sepByReads (spec: List Char → a → Prop) (separator: List Char → () → Prop) (read: List Char) (values: List a) (h: SepBy spec separator read values):
    ∃ (reads: List (List Char)) => List.All2 spec reads values :=
  match h with
    | Witness first (Witness rest (Witness firstRead (Witness restRead (Both same (Both split (Both valid each)))))) =>
      match eachSeparated spec separator restRead rest each with
        | Witness reads all => rewrite same in Witness [firstRead, ..reads] (Both valid all)

--| A person's line: at least one letter, all questions, and the person's
--| answers hold those letters and no others.
def PersonWritten (read: List Char) (person: Person): Prop :=
  read ≠ [] ∧ read.all isQuestion = True ∧ ((question: Char) → person.answers.contains question = read.contains question)

--| A group's lines.
def GroupWritten (read: List Char) (group: Group): Prop := SepBy PersonWritten (line u => Parse.LineBreak line) read group.people

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
  Parse.readsThen (() => Parse.many1 (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion)) _ _ _
    (Parse.readsMany1 _ _ (Parse.readsSatisfy _ _)) (lettersRead letters (Both each nonEmpty) =>
      match eachLetters lettersRead letters each with
        | Both same questions =>
          Parse.readsDone ({ answers = Set.fromList letters }: Person) _
            (rewrite List.appendNil lettersRead, same in
              Both (nonEmpty) (Both questions (question => containsFromList letters question))))

theorem readsGroup: Parse.Reads group GroupWritten :=
  Parse.readsThen (() => Parse.lines person) _ _ _ (readsSepBy1 person Parse.newline _ _ readsPerson Parse.readsNewline) (peopleRead people written =>
    Parse.readsDone ({ people }: Group) _ (rewrite List.appendNil peopleRead in written))

--| If `parseGroups` reads `input` as `groups`, the input is `groups` written out: the
--| groups' lines with a blank line between groups, then any line breaks.
theorem parseWritten (input: Text) (groups: List Group) (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ SepBy GroupWritten (blank u => Parse.BlankLine blank) read groups
        ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  Parse.allReads input (() => Parse.sections group) _ groups parsed (readsSepBy1 group Parse.blankLine _ _ readsGroup Parse.readsBlankLine)
