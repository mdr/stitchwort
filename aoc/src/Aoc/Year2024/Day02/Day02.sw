-- Advent of Code 2024, day 2: reports of reactor levels, one report per line.
-- A report is safe if its levels only rise or only fall, by one to three at
-- each step. Part 1 counts the safe reports; part 2 also counts those that
-- are safe once some single level is removed.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day02.main < inputs/2024/day02.txt
--
-- The proofs are in `Aoc.Year2024.Day02.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day02.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day02
import Aoc.Common (parseLines)
import Std (Fail, IO, List, Nat, Text)

def main(): {IO, Fail} () :=
  let reports := parseReports IO.readAllLines()
  IO.print "Part 1: ${solvePart1 reports}"
  IO.print "Part 2: ${solvePart2 reports}"

-- One line of the input: its levels in order.
type Report = { levels: List Nat }

-- One report per line, its levels separated by spaces: "7 6 4 2 1". A failure
-- names the line.
def parseReports (lines: List Text): {Fail} (List Report) := parseLines lines parseReport

def parseReport (line: Text): {Fail} Report :=
  let levels := line.words.map Text.toNatOrFail
  Fail.ensure (levels != []) "expected levels like '7 6 4 2 1', got an empty line"
  { levels }

-- Each level paired with the next one.
def steps (levels: List Nat): List (Nat, Nat) := levels.zip levels.tailOf

-- From `lower` to `higher` is a rise of one to three.
def risesGently (lower: Nat) (higher: Nat): Bool := lower < higher && higher <= lower + 3

-- Every step rises gently, or every step falls gently.
def isSafe (report: Report): Bool :=
  let reportSteps := steps report.levels
  reportSteps.all (step => risesGently step.fst step.snd) || reportSteps.all (step => risesGently step.snd step.fst)

-- The report with one level taken out, for each level in turn.
def withoutOneLevel (report: Report): List Report :=
  List.range report.levels.length |> .map (index => { levels = report.levels.removeAt index })

-- Safe as it is, or once one level is taken out.
def isSafeWithDampener (report: Report): Bool := isSafe report || (withoutOneLevel report |> .any isSafe)

def solvePart1 (reports: List Report): Nat := reports.count isSafe

def solvePart2 (reports: List Report): Nat := reports.count isSafeWithDampener
