--| The converse of `Parse.sw`: input that is groups of people's lines, written
--| out as the puzzle has them, is read as those groups.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Set, Text, Void)

theorem runsAsValue ∀ (p: () → {Parse} a) (read rest: List Char) (v w: a)
    (same: v = w)
    (runs: Parse.Runs p read rest v):
    Parse.Runs p read rest w :=
  rewrite same at runs in runs

theorem declinesLetter ∀ (rest: List Char)
    (stops: Parse.CannotStart isQuestion rest):
    Parse.Declines (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion) rest :=
  match rest with
    | [] => Parse.declinesSatisfyEnd _ _
    | [char, ..more] => Parse.declinesSatisfy _ _ char more (stops char more rfl)

theorem runsPerson ∀ (read: List Char) (who: Person)
    (written: PersonWritten read who) (rest: List Char)
    (stops: Parse.CannotStart isQuestion rest):
    Parse.Runs person read rest who :=
  match written with
    | Both nonEmpty (Both questions same) =>
      match read with
        | [] => Void.exfalso (nonEmpty rfl)
        | [letter, ..more] =>
          let sameAnswers: [letter, ..more].toSet = who.answers :=
            Set.ext _ _ (question => Eq.trans (containsFromList [letter, ..more] question) (Eq.sym (same question)))
          let sameSet: ({ answers = [letter, ..more].toSet }: Person) = who := match who with
            | { answers } => rewrite sameAnswers in rfl
          let lettersRun :=
            Parse.runsMany1Symbols
              (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion)
              (letter2 => letter2)
              isQuestion
              (letter2 after ok => Parse.runsSatisfy _ _ letter2 after ok)
              declinesLetter
              letter
              more
              rest
              (rewrite List.mapId more in questions)
              stops
          let lettersRead := rewrite List.mapId more at lettersRun in lettersRun
          runsAsValue person
            [letter, ..more]
            rest _
            who
            sameSet
            (Parse.runsMap
              (() => Parse.many1 (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion)) _
              [letter, ..more]
              rest
              (NonEmptyList.cons letter more)
              lettersRead)

theorem spaceNotQuestion ∀ (char: Char) (isSpace: Parse.isSpace char = True): isQuestion char = False :=
  match isSpace with
    | Inl space => rewrite space.read in rfl
    | Inr tab => rewrite tab.read in rfl

theorem declinesPerson ∀ (rest: List Char) (stops: Parse.CannotStart isQuestion rest): Parse.Declines person rest :=
  Parse.declinesBind
    (() => Parse.many1 (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion)) _
    rest
    (Parse.declinesMany1 _ rest (declinesLetter rest stops))

theorem declinesGroup ∀ (rest: List Char) (stops: Parse.CannotStart isQuestion rest): Parse.Declines group rest :=
  Parse.declinesBind
    (() => Parse.lines person) _
    rest
    (Parse.declinesSepBy1 person Parse.newline rest (declinesPerson rest stops))

theorem runsGroup ∀ (read: List Char) (who: Group)
    (written: GroupWritten read who) (rest: List Char)
    (end: Parse.LinesEnd rest):
    Parse.Runs group read rest who :=
  match who, written with
    | { people }, written2 =>
      match people, written2 with
        | { head = first, tail = others }, written3 =>
          Parse.runsMap
            (() => Parse.lines person)
            (people => { people })
            read
            rest
            (NonEmptyList.cons first others)
            (Parse.runsLinesOf person PersonWritten
              (Parse.CannotStart isQuestion)
              rest
              (read2 v after ok stops => runsPerson read2 v ok after stops)
              (read2 after isBreak => Parse.cannotStartAfterBreak isQuestion rfl rfl read2 after isBreak)
              (Parse.cannotStartAtLinesEnd isQuestion rfl rfl spaceNotQuestion rest end)
              (Parse.declinesLinesAtLinesEnd person isQuestion declinesPerson rfl rfl spaceNotQuestion rest end)
              read
              first
              others
              written3)

theorem runsSections ∀ (read: List Char) (first: Group) (others: List Group)
    (written: Parse.SepBy GroupWritten (read2 u => Parse.BlankLine read2) read (NonEmptyList.cons first others))
    (ending: List Char)
    (breaks: Parse.OnlyBreaks ending):
    Parse.Runs (() => Parse.sections group) read ending (NonEmptyList.cons first others) :=
  Parse.runsSectionsOf group GroupWritten Parse.LinesEnd ending
    (read2 v after ok end => runsGroup read2 v ok after end)
    Parse.linesEndAfterBlank
    (Parse.linesEndAtBreaks ending breaks)
    (Parse.declinesSectionsAtBreaks group isQuestion declinesGroup rfl rfl ending breaks)
    read
    first
    others
    written

--| The soundness theorem's conclusion: the input is groups written out, a
--| blank line between each two, then any line breaks.
def InputWritten (input: Text) (groups: List Group): Prop :=
  ∃ (read: List Char) => ∃ (ending: List Char) => input.toList = read ++ ending
    ∧ (∃ (listed: NonEmptyList Group) => Parse.SepBy GroupWritten (read2 u => Parse.BlankLine read2) read listed
      ∧ groups = listed.toList)
    ∧ ending.all (char => char == '\n' ∨ char == '\r') = True

--| Input that is groups written out is read as those groups.
theorem parseComplete ∀ (input: Text) (groups: List Group)
    (written: InputWritten input groups):
    Fail.toResult (() => parseGroups input) = Ok groups :=
  match written with
    | Witness read (Witness ending (Both split (Both (Witness listed (Both listedWritten same)) breaks))) =>
      match listed, listedWritten, same with
        | { head, tail }, listedWritten2, same2 =>
          Parse.runsAll input
            (() => Parse.sections group |> .toList)
            read
            ending
            groups
            split
            breaks
            (runsAsValue
              (() => Parse.sections group |> .toList)
              read
              ending _
              groups
              (Eq.sym same2)
              (Parse.runsMap
                (() => Parse.sections group)
                NonEmptyList.toList
                read
                ending
                (NonEmptyList.cons head tail)
                (runsSections read head tail listedWritten2 ending breaks)))

--| Soundness (`parseWritten`) is the converse: the input is written as at most one list of groups.
theorem writtenUnique ∀ (input: Text) (a b: List Group)
    (writtenA: InputWritten input a)
    (writtenB: InputWritten input b):
    a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
