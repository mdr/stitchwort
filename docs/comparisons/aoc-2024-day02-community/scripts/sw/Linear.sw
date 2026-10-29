-- Day 2 part 2 in linear time, for comparison with the committed brute force
-- (aoc/src/Aoc/Year2024/Day02). For one direction, only the two levels of the
-- first bad step can be the one to remove: removing any other level keeps
-- that step. So each direction needs at most three passes, not one per level.
--
--   $ stitchwort run Scratch.Linear.main < inputs/2024/day02.txt

namespace Scratch.Linear
import Aoc.Year2024.Day02 (..)
import Std (Bool, Fail, IO, List, Nat, Option)

-- Every step passes `ok` once at most one level is removed.
def toleratesOne (levels: List Nat) (ok: Nat → Nat → Bool): Bool :=
  match levels.zipWithNext.findIndex (step => Bool.not (ok step.fst step.snd)) with
    | None => True
    | Some index => (levels.removeAt index).chain ok || (levels.removeAt (index + 1)).chain ok

def isSafeLinear (report: Report): Bool :=
  toleratesOne report.levels risesGently || toleratesOne report.levels (level next => risesGently next level)

def main(): {IO, Fail} () :=
  let reports := parseReports IO.readAll()
  IO.print "Part 2 (linear): ${reports.count isSafeLinear}"

-- Only part 2 by the committed brute force, for timing against the above.
def mainBrute(): {IO, Fail} () :=
  let reports := parseReports IO.readAll()
  IO.print "Part 2 (brute): ${solvePart2 reports}"

-- Only the parse, to separate it from the checks.
def mainParse(): {IO, Fail} () :=
  let reports := parseReports IO.readAll()
  IO.print "Reports: ${reports.length}"
