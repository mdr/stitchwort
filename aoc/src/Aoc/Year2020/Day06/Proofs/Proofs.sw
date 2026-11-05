--| Day 6 proved: on any input the parser reads, each group's `anyone` and
--| `everyone` sets hold the questions the puzzle counts (Sets.sw), so both
--| parts are the spec's sums over the groups of lines the input is made of.

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Aoc.Year2020.Day06 (Spec)
import Std (Bool, Char, Eq, Exists, Fail, List, Nat, Parse, Result, Set, Text, Void)

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
  sumCounts .anyone.size (Spec.count Spec.anyone) anyoneCount lineGroups groups written

theorem part2Lines (lineGroups: List (List (List Char))) (groups: List Group) (written: List.All2 GroupLines lineGroups groups):
    solvePart2 groups = lineGroups.sumBy (Spec.count Spec.everyone) :=
  sumCounts .everyone.size (Spec.count Spec.everyone) everyoneCount lineGroups groups written

--| The groups the parser reads are the input's, as groups of lines: the
--| input is them written out, a blank line (spaces and tabs allowed) between
--| each two, then any line breaks, and each group's people are those lines.
theorem inputGroups (input: Text) (groups: List Group) (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (lineGroups: List (List (List Char))) => ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ SepByList LinesWritten (read u => Parse.BlankLine read) read lineGroups
        ∧ ending.all (char => char == '\n' ∨ char == '\r') = True ∧ List.All2 GroupLines lineGroups groups :=
  match parseWritten input groups parsed with
    | Witness read (Witness ending (Both text (Both written done))) =>
      match sepByMap GroupWritten LinesWritten GroupLines _
          (groupRead group groupWritten => sepByMap PersonWritten (line written => line = written) (line person => PersonWritten line person) _
            (personRead person personWritten => Witness personRead (Both rfl personWritten)) groupRead group.people groupWritten)
          read groups written with
        | Witness lineGroups (Both linesRead related) => Witness lineGroups (Witness read (Witness ending (Both text (Both linesRead (Both done related)))))

--| Part 1, for every input the parser reads, is the spec's sum over the
--| groups of lines the input is made of.
theorem part1Correct (input: Text) (groups: List Group) (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (lineGroups: List (List (List Char))) => ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ SepByList LinesWritten (read u => Parse.BlankLine read) read lineGroups
        ∧ ending.all (char => char == '\n' ∨ char == '\r') = True ∧ solvePart1 groups = Spec.part1Answer lineGroups :=
  match inputGroups input groups parsed with
    | Witness lineGroups (Witness read (Witness ending (Both text (Both linesRead (Both done related))))) =>
      Witness lineGroups (Witness read (Witness ending (Both text (Both linesRead (Both done (part1Lines lineGroups groups related))))))

theorem part2Correct (input: Text) (groups: List Group) (parsed: Fail.toResult (() => parseGroups input) = Ok groups):
    ∃ (lineGroups: List (List (List Char))) => ∃ (read: List Char) => ∃ (ending: List Char) =>
      input.toList = read ++ ending ∧ SepByList LinesWritten (read u => Parse.BlankLine read) read lineGroups
        ∧ ending.all (char => char == '\n' ∨ char == '\r') = True ∧ solvePart2 groups = Spec.part2Answer lineGroups :=
  match inputGroups input groups parsed with
    | Witness lineGroups (Witness read (Witness ending (Both text (Both linesRead (Both done related))))) =>
      Witness lineGroups (Witness read (Witness ending (Both text (Both linesRead (Both done (part2Lines lineGroups groups related))))))
