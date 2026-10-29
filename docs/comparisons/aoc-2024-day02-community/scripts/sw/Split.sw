-- Day 2 parsed by splitting into lines and words instead of with `Parse`, to
-- see how much of the run time is the parser. Bad numbers are dropped, not
-- reported, so this is for timing only.
--
--   $ stitchwort run Scratch.Split.main < inputs/2024/day02.txt

namespace Scratch.Split
import Aoc.Year2024.Day02 (..)
import Std (IO, List, Nat, Text)

def splitReports (input: Text): List Report :=
  input.lines |> .map (line => ({ levels = line.words.filterMap Text.toNat }: Report))

def main(): {IO} () :=
  let reports := splitReports IO.readAll()
  IO.print "Part 1: ${solvePart1 reports}"
  IO.print "Part 2: ${solvePart2 reports}"

def mainParse(): {IO} () :=
  let reports := splitReports IO.readAll()
  IO.print "Reports: ${reports.length}"
