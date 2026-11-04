--| Advent of Code 2020, day 5: boarding passes, each ten letters that halve
--| the plane's 128 rows (`F` front, `B` back) and then its 8 columns (`L`
--| left, `R` right) down to one seat, whose ID is its row times 8 plus its
--| column. Part 1 is the highest seat ID on a pass; part 2 your seat, the
--| one missing ID whose neighbours either side are on passes.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day05.main < inputs/2020/day05.txt
--|
--| The program reads a pass as a 10-bit binary number, with `B` and `R` as
--| 1. The proofs, that this is the seat ID the halving gives and that both
--| answers are the puzzle's, are in `Aoc.Year2020.Day05.Proofs` (Proofs/),
--| and the tests in `Aoc.Year2020.Day05.Tests` (Tests/); `run` checks
--| neither.

namespace Aoc.Year2020.Day05
import Std (Char, Fail, IO, List, Nat, Option, Parse, Text)

def main(): {IO, Fail} () :=
  let passes := parsePasses IO.readAll()
  IO.print "Part 1: ${solvePart1 passes |> .fold "no boarding passes" (id => "${id}")}"
  IO.print "Part 2: ${solvePart2 passes |> .fold "no missing seat between two passes" (id => "${id}")}"

--| One letter, `True` for `upper`.
def half (lower: Char) (upper: Char): {Parse} Bool :=
  Parse.satisfy "'${lower}' or '${upper}'" (letter => letter == lower || letter == upper) == upper

def frontBack(): {Parse} Bool := half 'F' 'B'

def leftRight(): {Parse} Bool := half 'L' 'R'

--| A pass's bits, the most significant first.
def pass(): {Parse} List Bool :=
  let row := Parse.repeat 7 7 frontBack
  let column := Parse.repeat 3 3 leftRight
  row ++ column

def parsePasses (input: Text): {Fail} List (List Bool) := Parse.eachLine input pass

def seatId (pass: List Bool): Nat := Nat.fromBits pass

def solvePart1 (passes: List (List Bool)): Option Nat := (passes.map seatId).maximum

--| In a sorted list, the first number missing between two that are 2 apart.
def gap: List Nat → Option Nat
  | [low, high, ..rest] => if high == low + 2 then Some (low + 1) else gap [high, ..rest]
  | _ => None

def solvePart2 (passes: List (List Bool)): Option Nat := (passes.map seatId).sort |> gap
