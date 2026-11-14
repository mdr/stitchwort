--| Day 5 as the puzzle states it, on the passes as written. The proofs
--| (Proofs/) show the program's answers are these.

namespace Aoc.Year2020.Day05.Spec
import Std (Char, List, Nat, Option)

--| "Rows 0 through 127": the rows or columns from `first` to `last`, both
--| included.
type Region = { first: Nat, last: Nat }

def Region.size (region: Region): Nat := region.last + 1 - region.first

--| "Keep the lower half."
def Region.lowerHalf (region: Region): Region := { first = region.first, last = region.first + region.size / 2 - 1 }

--| "Keep the upper half."
def Region.upperHalf (region: Region): Region := { first = region.first + region.size / 2, last = region.last }

--| "Each letter tells you which half of a region the given seat is in":
--| `lower` keeps the lower half, `upper` the upper; any other letter isn't
--| a pass.
def narrow (lower upper: Char) (region: Region): List Char → Option Region
  | [] => Some region
  | [letter, ..rest] =>
    if letter == lower then narrow lower upper region.lowerHalf rest
    else if letter == upper then narrow lower upper region.upperHalf rest
    else None

--| "Until you're left with exactly one row."
def Region.only (region: Region): Option Nat := if region.first == region.last then Some region.first else None

--| "The first 7 characters will either be F or B; these specify exactly one
--| of the 128 rows on the plane (numbered 0 through 127) … F means to take
--| the lower half, … B means to take the upper half."
def row (letters: List Char): Option Nat := (narrow 'F' 'B' { first = 0, last = 127 } letters).flatMap Region.only

--| "The last three characters will be either L or R; these specify exactly
--| one of the 8 columns of seats on the plane (numbered 0 through 7) … L
--| means to keep the lower half, while R means to keep the upper half."
def column (letters: List Char): Option Nat := (narrow 'L' 'R' { first = 0, last = 7 } letters).flatMap Region.only

type Seat = { row: Nat, column: Nat }

--| The seat a pass of 7 row letters and 3 column letters specifies.
def seat (pass: List Char): Option Seat :=
  if pass.length == 10 then
    (row (pass.take 7), column (pass.drop 7)) |> match some | (Some row, Some column) => ({ row, column })
  else None

--| "Every seat also has a unique seat ID: multiply the row by 8, then add
--| the column."
def Seat.id (seat: Seat): Nat := seat.row * 8 + seat.column

def seatIds (passes: List (List Char)): List Nat := passes.filterMap (pass => (seat pass).map Seat.id)

--| "What is the highest seat ID on a boarding pass?"
def part1Answer (passes: List (List Char)): Option Nat := (seatIds passes).maximum

--| "Your seat wasn't at the very front or back, though; the seats with IDs
--| +1 and -1 from yours will be in your list", and yours isn't.
def isYourSeat (ids: List Nat) (id: Nat): Bool := not (ids.contains id) ∧ ids.contains (id + 1) ∧ ids.contains (id - 1)

--| "What is the ID of your seat?": every seat ID that could be yours, from
--| the 128 × 8 seats. The puzzle promises one.
def part2Answers (passes: List (List Char)): List Nat := (List.range 0 (128 * 8)).filter (isYourSeat (seatIds passes))
