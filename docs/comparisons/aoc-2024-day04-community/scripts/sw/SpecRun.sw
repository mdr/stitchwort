-- Day 4's spec (aoc/src/Aoc/Year2024/Day04/Spec/Spec.sw), copied as it is,
-- run as a program on the real input: how slow is the position-by-position
-- reading, with a list lookup for every letter?

namespace Scratch.SpecRun
import Std (Bool, IO, List, Nat, Option, Text)

type Grid = { rows: List (List Char) }

def letterAt (grid: Grid) (r: Nat) (c: Nat): Option Char := grid.rows.getOr r [] |> .get c

type Step =
  | Back
  | Stay
  | Ahead

type Direction = { down: Step, across: Step }

def directions: List Direction := [
  { down = Back, across = Back },
  { down = Back, across = Stay },
  { down = Back, across = Ahead },
  { down = Stay, across = Back },
  { down = Stay, across = Ahead },
  { down = Ahead, across = Back },
  { down = Ahead, across = Stay },
  { down = Ahead, across = Ahead }
]

def moved (start: Nat) (step: Step) (distance: Nat): Option Nat :=
  match step with
    | Back => if distance ≤ start then Some (start - distance) else None
    | Stay => Some start
    | Ahead => Some (start + distance)

def letterAlong (grid: Grid) (r: Nat) (c: Nat) (direction: Direction) (distance: Nat): Option Char :=
  match moved r direction.down distance, moved c direction.across distance with
    | Some row, Some column => letterAt grid row column
    | _, _ => None

def spells (word: List Char) (grid: Grid) (r: Nat) (c: Nat) (direction: Direction): Bool :=
  List.range word.length |> .all (distance => letterAlong grid r c direction distance == word.get distance)

def countPositions (grid: Grid) (p: Nat → Nat → Nat): Nat :=
  List.range grid.rows.length |> .sumBy (r => List.range (grid.rows.getOr r []).length |> .sumBy (c => p r c))

def part1Spec (grid: Grid): Nat :=
  countPositions grid (r c => directions.count (spells ['X', 'M', 'A', 'S'] grid r c))

def masThrough (grid: Grid) (r: Nat) (c: Nat) (start: Direction) (end: Direction): Bool :=
  let letters := [letterAlong grid r c start 1, letterAt grid r c, letterAlong grid r c end 1]
  letters == [Some 'M', Some 'A', Some 'S'] ∨ letters == [Some 'S', Some 'A', Some 'M']

def crossAt (grid: Grid) (r: Nat) (c: Nat): Bool :=
  masThrough grid r c { down = Back, across = Back } { down = Ahead, across = Ahead }
    ∧ masThrough grid r c { down = Back, across = Ahead } { down = Ahead, across = Back }

def part2Spec (grid: Grid): Nat := countPositions grid (r c => Bool.toNat (crossAt grid r c))

def main(): {IO} () :=
  let grid: Grid := { rows = IO.readAllLines() |> .map Text.toList }
  IO.print "Part 1: ${part1Spec grid}"
  IO.print "Part 2: ${part2Spec grid}"
