--| Day 6 proved: on any input the parser reads, each group's `anyone` and
--| `everyone` sets hold the questions the puzzle counts (Sets.sw), so both
--| parts are the puzzle's sums.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Aoc.Year2020.Day06 (Spec)
import Std (Bool, Char, Eq, Exists, Fail, List, Nat, Parse, Result, Set, Text, Void)

--| A group as the lines its people wrote.
def GroupLines (lines: List (List Char)) (group: Group): Prop := List.All2 PersonWritten lines group.people

theorem anyoneCount (lines: List (List Char)) (group: Group) (written: GroupLines lines group):
    group.anyone.size = Spec.count Spec.anyone lines :=
  let agree: (question: Char) → group.anyone.contains question = Spec.anyone lines question :=
    question => unionContains lines group.people written Set.empty question
  sizeCount group.anyone (Spec.anyone lines)
    (question found => anyQuestion lines group.people written question (rewrite agree question at found in found))
    (question isQuestion => agree question)

theorem everyoneCount (lines: List (List Char)) (group: Group) (written: GroupLines lines group):
    group.everyone.size = Spec.count Spec.everyone lines :=
  let meet: (question: Char) → group.everyone.contains question = ((Set.fromList questions).contains question ∧ Spec.everyone lines question) :=
    question => intersectContains lines group.people written (Set.fromList questions) question
  sizeCount group.everyone (Spec.everyone lines)
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

theorem part1Correct (lineGroups: List (List (List Char))) (groups: List Group) (written: List.All2 GroupLines lineGroups groups):
    solvePart1 groups = Spec.part1Answer lineGroups :=
  sumCounts (group => group.anyone.size) (Spec.count Spec.anyone) anyoneCount lineGroups groups written

theorem part2Correct (lineGroups: List (List (List Char))) (groups: List Group) (written: List.All2 GroupLines lineGroups groups):
    solvePart2 groups = Spec.part2Answer lineGroups :=
  sumCounts (group => group.everyone.size) (Spec.count Spec.everyone) everyoneCount lineGroups groups written

theorem groupLines: (reads: List (List Char)) → (groups: List Group) → List.All2 GroupWritten reads groups → ∃ (lineGroups: List (List (List Char))) => List.All2 GroupLines lineGroups groups
  | [], [], all => Witness [] ()
  | [read, ..reads], [group, ..groups], Both written rest =>
    match sepByReads PersonWritten (line u => Parse.LineBreak line) read group.people written, groupLines reads groups rest with
      | Witness lines linesWritten, Witness lineGroups all => Witness [lines, ..lineGroups] (Both linesWritten all)
  | [], [_, .._], impossible => Void.exfalso impossible
  | [_, .._], [], impossible => Void.exfalso impossible

--| When `parseGroups` reads `input` (`parseWritten` says how the input is
--| those groups written out), both parts are the puzzle's sums over the
--| groups' lines.
theorem correct (input: Text) (groups: List Group) (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (lineGroups: List (List (List Char))) => List.All2 GroupLines lineGroups groups ∧ solvePart1 groups = Spec.part1Answer lineGroups ∧ solvePart2 groups = Spec.part2Answer lineGroups :=
  match parseWritten input groups parsed with
    | Witness read (Witness ending (Both split (Both separated endings))) =>
      match sepByReads GroupWritten (blank u => Parse.BlankLine blank) read groups separated with
        | Witness reads all =>
          match groupLines reads groups all with
            | Witness lineGroups written => Witness lineGroups (Both written (Both (part1Correct lineGroups groups written) (part2Correct lineGroups groups written)))
