-- Day 6, proved: the strict parser `main` uses gives the same problems as the
-- total parser the other proofs are about, whenever it accepts. So
-- `part1Correct` and `part2Correct` describe what `main` prints. Kept apart
-- from the program, so `stitchwort run Aoc.Day06.main` doesn't check it.

namespace Aoc.Day06.Proofs
import Aoc.Day06 (..)
import Std (Eq, List, Result, Text)

-- The accepted problems, or a fallback for a rejection.
def acceptedOr (fallback: List Problem): Result (List Problem) Text → List Problem
  | Ok problems => problems
  | Err message => fallback

theorem acceptedOrCheck (lines: List Text): acceptedOr (parseWorksheet lines) (checkWorksheet lines) = parseWorksheet lines :=
  match worksheetError lines with
    | Some message => rfl
    | None => rfl

-- Whenever `checkWorksheet` accepts, what it gives is `parseWorksheet lines`.
theorem checkWorksheetParses (lines: List Text) (problems: List Problem) (accepted: checkWorksheet lines = Ok problems):
    problems = parseWorksheet lines :=
  Eq.trans (Eq.sym (Eq.cong (acceptedOr (parseWorksheet lines)) accepted)) (acceptedOrCheck lines)
