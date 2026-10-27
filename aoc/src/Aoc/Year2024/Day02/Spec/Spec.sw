-- Day 2 as the puzzle states it. The proofs (Proofs/) show the program
-- computes these, for every list of reports.

namespace Aoc.Year2024.Day02.Spec
import Aoc.Year2024.Day02 (..)
import Std (List, Nat)

-- "The levels are either all increasing or all decreasing": each level
-- against the next.
def allIncreasing (levels: List Nat): Bool := levels.chain (level next => level < next)

def allDecreasing (levels: List Nat): Bool := levels.chain (level next => level > next)

-- "Any two adjacent levels differ by at least one and at most three."
def differByOneToThree (level: Nat) (next: Nat): Bool := 1 <= Nat.absDiff level next && Nat.absDiff level next <= 3

def adjacentDifferByOneToThree (levels: List Nat): Bool := levels.chain differByOneToThree

-- "A report only counts as safe if both of the following are true."
def safe (report: Report): Bool :=
  (allIncreasing report.levels || allDecreasing report.levels) && adjacentDifferByOneToThree report.levels

-- "If removing a single level from an unsafe report would make it safe, the
-- report instead counts as safe."
def safeWithDampener (report: Report): Bool :=
  safe report || (List.range report.levels.length |> .any (index => safe { levels = report.levels.removeAt index }))

-- "How many reports are safe?"
def safeReports (reports: List Report): Nat := reports.count safe

def safeReportsWithDampener (reports: List Report): Nat := reports.count safeWithDampener
