--| Day 6 proved: on any input the parser reads, each group's `anyone` and
--| `everyone` sets hold the questions the puzzle counts (Sets.sw), and the
--| groups are those the spec splits the input's lines into (Split.sw), so
--| both parts are the spec's sums over the input.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Aoc.Year2020.Day06 (Spec)
import Std (Bool, Char, DecEq, Eq, Option, Exists, Fail, List, Nat, Parse, Result, Set, Text, Void)

--| A group as the lines its people wrote.
def GroupLines (lines: List (List Char)) (group: Group): Prop := List.All2 PersonWritten lines group.people

theorem anyoneCount (lines: List (List Char)) (group: Group) (written: GroupLines lines group):
    group.anyone.size = Spec.count Spec.anyone lines :=
  let agree: (question: Char) → group.anyone.contains question = Spec.anyone lines question :=
    question => Eq.trans (Set.containsUnions (group.people.map .answers) question) (anyAnswers lines group.people written question)
  Set.sizeOfMembers group.anyone Spec.questions (Spec.anyone lines) questionsDistinct
    (question found => anyQuestion lines group.people written question (rewrite agree question at found in found))
    (question isQuestion => agree question)

theorem everyoneCount (lines: List (List Char)) (group: Group) (written: GroupLines lines group):
    group.everyone.size = Spec.count Spec.everyone lines :=
  let meet: (question: Char) → group.everyone.contains question = ((Set.fromList questions).contains question ∧ Spec.everyone lines question) :=
    question => intersectContains lines group.people written (Set.fromList questions) question
  Set.sizeOfMembers group.everyone Spec.questions (Spec.everyone lines) questionsDistinct
    (question found =>
      let both := rewrite meet question at found in found
      rewrite containsFromList questions question at both in Bool.andLeft _ _ both)
    (question isQuestion => rewrite meet question, containsFromList questions question, isQuestion in rfl)

--| The sums over groups: a lemma over any per-group count, then the two
--| parts.
theorem sumCounts (size: Group → Nat) (count: List (List Char) → Nat) (each: (lines: List (List Char)) → (group: Group) → GroupLines lines group → size group = count lines):
    (lineGroups: List (List (List Char))) → (groups: List Group) → List.All2 GroupLines lineGroups groups → groups.sumBy size = lineGroups.sumBy count
  | [], [], all => rfl
  | [lines, ..lineGroups], [group, ..groups], Both written rest =>
    rewrite List.sumByCons groups group size, List.sumByCons lineGroups lines count, each lines group written, sumCounts size count each lineGroups groups rest in rfl
  | [], [_, .._], impossible => Void.exfalso impossible
  | [_, .._], [], impossible => Void.exfalso impossible

theorem part1Lines (lineGroups: List (List (List Char))) (groups: List Group) (written: List.All2 GroupLines lineGroups groups):
    solvePart1 groups = lineGroups.sumBy (Spec.count Spec.anyone) :=
  sumCounts (.anyone.size) (Spec.count Spec.anyone) anyoneCount lineGroups groups written

theorem part2Lines (lineGroups: List (List (List Char))) (groups: List Group) (written: List.All2 GroupLines lineGroups groups):
    solvePart2 groups = lineGroups.sumBy (Spec.count Spec.everyone) :=
  sumCounts (.everyone.size) (Spec.count Spec.everyone) everyoneCount lineGroups groups written

theorem spaceNotQuestion (char: Char) (space: (char == ' ' ∨ char == '\t') = True) (question: isQuestion char = True): Void :=
  Bool.orElim (char == ' ') (char == '\t') Void space
    (isSpace => Bool.falseNotTrue (rewrite DecEq.sound char ' ' isSpace at question in question))
    (isTab => Bool.falseNotTrue (rewrite DecEq.sound char '\t' isTab at question in question))

--| A line is blank for the spec exactly when the parser read it as blank.
theorem blankAgrees (read: List Char) (line: Option Person) (written: LineWritten read line): Spec.blank read = line.isNone :=
  match line with
    | None => written
    | Some person =>
      match read with
        | [] => Void.exfalso (And.left written rfl)
        | [char, ..rest] =>
          match space: char == ' ' ∨ char == '\t' with
            | True => Void.exfalso (spaceNotQuestion char space (Bool.andLeft _ _ (And.left (And.right written))))
            | False => rfl

theorem peopleLines: (lines: List (List Char)) → (lineGroup: List (Option Person)) → List.All2 LineWritten lines lineGroup → List.NonSep Option.isNone lineGroup →
    List.All2 PersonWritten lines (lineGroup.filterMap (answers => answers))
  | [], [], all, nonBlank => ()
  | [line, ..lines], [Some person, ..rest], Both written more, nonBlank => Both written (peopleLines lines rest more nonBlank)
  | [line, ..lines], [None, ..rest], Both written more, nonBlank => Void.exfalso (Bool.falseNotTrue nonBlank)
  | [], [_, .._], impossible, nonBlank => Void.exfalso impossible
  | [_, .._], [], impossible, nonBlank => Void.exfalso impossible

--| Between blank lines, the lines are people's.
theorem groupLines: (lineGroups: List (List (List Char))) → (groups: List (List (Option Person))) → List.All2 (List.All2 LineWritten) lineGroups groups →
    List.Groups Option.isNone groups → List.All2 GroupLines lineGroups (groups.map (people => { people = people.filterMap (answers => answers) }))
  | [], [], all, nonBlank => ()
  | [lines, ..lineGroups], [group, ..groups], Both written rest, Both (Both nonEmpty nonBlankGroup) nonBlankRest =>
    Both (peopleLines lines group written nonBlankGroup) (groupLines lineGroups groups rest nonBlankRest)
  | [], [_, .._], impossible, nonBlank => Void.exfalso impossible
  | [_, .._], [], impossible, nonBlank => Void.exfalso impossible

--| Part 1, for every input the parser reads, is the spec's sum over the
--| groups of lines of the input.
theorem part1Correct (input: Text) (groups: List Group) (parsed: Fail.toResult (() => parseGroups input) = Ok groups): solvePart1 groups = Spec.part1Answer input :=
  match linesOf input groups parsed with
    | Witness values (Both same written) => rewrite same in part1Lines _ _ (groupsWritten input values written)

theorem part2Correct (input: Text) (groups: List Group) (parsed: Fail.toResult (() => parseGroups input) = Ok groups): solvePart2 groups = Spec.part2Answer input :=
  match linesOf input groups parsed with
    | Witness values (Both same written) => rewrite same in part2Lines _ _ (groupsWritten input values written)

theorem linesOf (input: Text) (groups: List Group) (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (values: List (Option Person)) => groups = groupsOf values ∧ Fail.toResult (() => parseLines input) = Ok values :=
  match read: Fail.toResult (() => parseLines input) with
    | Ok values =>
      let split := rewrite Fail.toResultThen (() => parseLines input) groupsOf, read at parsed in parsed
      Witness values (Both (Eq.sym (Result.okInjective _ _ split)) rfl)
    | Err message =>
      let split := rewrite Fail.toResultThen (() => parseLines input) groupsOf, read at parsed in parsed
      Void.exfalso (Result.errNotOk _ groups split)

--| The groups of lines the spec reads from the input are those the parser
--| read the groups from.
theorem groupsWritten (input: Text) (values: List (Option Person)) (parsed: Fail.toResult (() => parseLines input) = Ok values):
    List.All2 GroupLines (Spec.groupsOf input) (groupsOf values) :=
  groupLines _ _
    (splitByRel LineWritten Spec.blank Option.isNone blankAgrees _ _ (parseWritten input values parsed))
    (List.splitByGroups values Option.isNone)
