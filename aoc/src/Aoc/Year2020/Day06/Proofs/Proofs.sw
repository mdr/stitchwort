--| Day 6 proved: on any input the parser reads, each group's `anyone` and
--| `everyone` sets hold the questions the puzzle counts (Sets.sw), so both
--| parts are the spec's sums over the groups of lines the input is made of.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Aoc.Year2020.Day06 (Spec)
import Std (Bool, Char, Eq, Exists, Fail, List, Nat, NonEmptyList, Parse, Result, Set, Text, Void)

--| A group as the lines its people wrote.
def GroupLines (lines: List (List Char)) (group: Group): Prop := List.All2 PersonWritten lines group.people.toList

theorem anyoneCount ∀ (lines: List (List Char)) (group: Group)
    (written: GroupLines lines group):
    group.anyone.size = Spec.count Spec.anyone lines :=
  let agree: ∀ (question: Char) => group.anyone.contains question = Spec.anyone lines question := question =>
    Eq.trans
      (NonEmptyList.containsUnionAll (group.people.map .answers) question)
      (anyAnswers lines group.people.toList written question)
  Set.sizeOfMembers group.anyone Spec.questions
    (Spec.anyone lines)
    questionsDistinct
    (question found =>
      anyQuestion lines group.people.toList written question (rewrite agree question at found in found))
    (question isQuestion => agree question)

theorem everyoneCount ∀ (lines: List (List Char)) (group: Group)
    (written: GroupLines lines group):
    group.everyone.size = Spec.count Spec.everyone lines :=
  let meet: ∀ (question: Char) => group.everyone.contains question = Spec.everyone lines question := question =>
    intersectContains lines group.people written question
  Set.sizeOfMembers group.everyone Spec.questions
    (Spec.everyone lines)
    questionsDistinct
    (question found =>
      everyQuestion lines group.people.toList written
        (NonEmptyList.toListNotNil group.people)
        question
        (rewrite meet question at found in found))
    (question isQuestion => meet question)

--| The sums over groups: a lemma over any per-group count, then the two
--| parts.
theorem sumCounts ∀ (size: Group → Nat) (count: List (List Char) → Nat)
    (each: ∀ (lines: List (List Char)) (group: Group) => GroupLines lines group → size group = count lines)
    (lineGroups: List (NonEmptyList (List Char))) (groups: List Group)
    (impossible: List.All2 (lines group => GroupLines lines.toList group) lineGroups groups):
    groups.sumBy size = lineGroups.sumBy (lines => count lines.toList) :=
  match lineGroups, groups, impossible with
    | [], [], all => rfl
    | [lines, ..lineGroups], [group, ..groups], Both written rest =>
      rewrite List.sumByCons groups group size,
          List.sumByCons lineGroups lines (lines => count lines.toList),
          each lines.toList group written,
          sumCounts size count each lineGroups groups rest in
        rfl
    | [], [_, .._], impossible => Void.exfalso impossible
    | [_, .._], [], impossible => Void.exfalso impossible

theorem part1Lines ∀ (lineGroups: List (NonEmptyList (List Char))) (groups: List Group)
    (written: List.All2 (lines group => GroupLines lines.toList group) lineGroups groups):
    solvePart1 groups = lineGroups.sumBy (lines => Spec.count Spec.anyone lines.toList) :=
  sumCounts .anyone.size (Spec.count Spec.anyone) anyoneCount lineGroups groups written

theorem part2Lines ∀ (lineGroups: List (NonEmptyList (List Char))) (groups: List Group)
    (written: List.All2 (lines group => GroupLines lines.toList group) lineGroups groups):
    solvePart2 groups = lineGroups.sumBy (lines => Spec.count Spec.everyone lines.toList) :=
  sumCounts .everyone.size (Spec.count Spec.everyone) everyoneCount lineGroups groups written

--| The groups the parser reads are the input's, as groups of lines: the
--| input is them written out, a blank line (spaces and tabs allowed) between
--| each two, then any line breaks, and each group's people are those lines.
theorem inputGroups ∀ (input: Text) (groups: List Group)
    (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (lineGroups: NonEmptyList (NonEmptyList (List Char))) => ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending
        ∧ Parse.SepBy LinesWritten (read u => Parse.BlankLine read) read lineGroups
        ∧ ending.all (char => char == '\n' ∨ char == '\r') = True
        ∧ List.All2 (lines group => GroupLines lines.toList group) lineGroups.toList groups :=
  match parseWritten input groups parsed with
    | Witness read (Witness ending (Both text (Both (Witness listed (Both written same)) done))) =>
      match Parse.sepByMap GroupWritten LinesWritten
        (lines group => GroupLines lines.toList group) _
        (groupRead group groupWritten =>
          Parse.sepByMap PersonWritten
            (line written => line = written)
            (line person => PersonWritten line person) _
            (personRead person personWritten => Witness personRead (Both rfl personWritten))
            groupRead
            group.people
            groupWritten)
        read
        listed
        written with
        | Witness lineGroups (Both linesRead related) =>
          Witness lineGroups
            (Witness read (Witness ending (Both text (Both linesRead (Both done (rewrite same in related))))))

--| Part 1, for every input the parser reads, is the spec's sum over the
--| groups of lines the input is made of.
theorem part1Correct ∀ (input: Text) (groups: List Group)
    (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (lineGroups: NonEmptyList (NonEmptyList (List Char))) => ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending
        ∧ Parse.SepBy LinesWritten (read u => Parse.BlankLine read) read lineGroups
        ∧ ending.all (char => char == '\n' ∨ char == '\r') = True
        ∧ solvePart1 groups = Spec.part1Answer (lineGroups.toList.map NonEmptyList.toList) :=
  match inputGroups input groups parsed with
    | Witness lineGroups (Witness read (Witness ending (Both text (Both linesRead (Both done related))))) =>
      Witness lineGroups
        (Witness read
          (Witness ending
            (Both text
              (Both linesRead
                (Both done
                  (rewrite part1Lines lineGroups.toList groups related,
                      List.sumByMap lineGroups.toList (Spec.count Spec.anyone) NonEmptyList.toList in
                    rfl))))))

theorem part2Correct ∀ (input: Text) (groups: List Group)
    (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (lineGroups: NonEmptyList (NonEmptyList (List Char))) => ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending
        ∧ Parse.SepBy LinesWritten (read u => Parse.BlankLine read) read lineGroups
        ∧ ending.all (char => char == '\n' ∨ char == '\r') = True
        ∧ solvePart2 groups = Spec.part2Answer (lineGroups.toList.map NonEmptyList.toList) :=
  match inputGroups input groups parsed with
    | Witness lineGroups (Witness read (Witness ending (Both text (Both linesRead (Both done related))))) =>
      Witness lineGroups
        (Witness read
          (Witness ending
            (Both text
              (Both linesRead
                (Both done
                  (rewrite part2Lines lineGroups.toList groups related,
                      List.sumByMap lineGroups.toList (Spec.count Spec.everyone) NonEmptyList.toList in
                    rfl))))))
