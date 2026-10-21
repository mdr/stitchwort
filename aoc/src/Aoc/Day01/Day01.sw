-- Advent of Code 2025, day 1: a dial numbered 0 to 99 starts at 50 and is
-- turned left or right. Part 1 counts the turns that end on 0; part 2 counts
-- every click that lands on 0, including those in the middle of a turn.
--
--   $ cd aoc && stitchwort run Aoc.Day01.main < inputs/day01.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- The dial's size is a parameter, `highest` being its largest number (99 in
-- the puzzle). Part 2 is proved correct, for a dial of any size, in
-- `Aoc.Day01.Proofs` (Proofs/Part2.sw), which `run` does not check.

namespace Aoc.Day01
import Std (IO, Int, List)

def main(): {IO} () :=
  let turns := parseTurns (IO.readAllLines())
  IO.print "Part 1: ${solvePart1 turns}"
  IO.print "Part 2: ${solvePart2 turns}"

def parseTurns (lines: List Text): List Turn := lines.filterMap Turn.parse

def solvePart1 (turns: List Turn): Nat := zerosLandedOn dial turns

def solvePart2 (turns: List Turn): Nat := zerosPassed dial turns

-- The puzzle's dial, at 50.
def dial: Dial 99 := { position = 50, inRange = rfl }

def example: List Text := """
  L68
  L30
  R48
  L5
  R60
  L55
  L1
  L99
  R14
  L82
  """.lines

test "example" := (solvePart1 (parseTurns example), solvePart2 (parseTurns example)) == (3, 6)

-- Part 1: the positions after each turn that are 0.
def zerosLandedOn (start: Dial highest) (turns: List Turn): Nat :=
  turns
    |> .scanLeft Dial.move start
    |> .drop 1
    |> .count Dial.isZero

-- Part 2: for each turn, the clicks onto 0 from where the dial was before it.
def zerosPassed (start: Dial highest) (turns: List Turn): Nat :=
  turns
    |> .scanLeft Dial.move start
    |> .zipWith Dial.zerosDuring turns
    |> .sum

type Turn =
  | Left (distance: Nat)
  | Right (distance: Nat)

-- "L68" is `Left 68`.
def Turn.parse (t: Text): Option Turn :=
  match t.uncons with
    | Some ('L', rest) => rest.toNat.map Left
    | Some ('R', rest) => rest.toNat.map Right
    | _                => None

def after (t: Text): Option Nat := (Turn.parse t).map (turn => (dial.move turn).position)

test "parse" := after "L68" == Some 82
test "parse right" := after "R5" == Some 55
test "parse junk" := after "X5" == None

-- A turn, one click at a time: `Left 3` is three `Left 1`s. Only the
-- specification of part 2 and its proofs (`Aoc.Day01.Proofs`) use it; it stays
-- here so that they can write `t.clicks`, a dot name must live with its type.
def Turn.clicks: Turn -> List Turn
  | Left n  => List.replicate n (Left 1)
  | Right n => List.replicate n (Right 1)

-- A dial numbered 0 to `highest`, at `position`.
type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }

-- Any integer, wrapped onto the dial.
def Dial.fromInt (highest: Nat) (x: Int): Dial highest :=
  { position = Int.modNat x (Succ highest), inRange = Int.modNatLt x (Succ highest) }

-- The number of positions on the dial.
def Dial.size (d: Dial highest): Nat := Succ highest

-- Where a turn leaves the dial.
def Dial.move (d: Dial highest): Turn -> Dial highest
  | Left n  => Dial.fromInt highest (d.position.toInt - n.toInt)
  | Right n => Dial.fromInt highest (d.position.toInt + n.toInt)

def Dial.isZero (d: Dial highest): Bool := d.position == 0

-- How many clicks of a turn land on 0. Going right from `d`, the dial is at
-- 0 after each click that brings `d + k` to a multiple of the dial's size.
-- Going left is the mirror image: 0 is `(size - d) % size` clicks away.
def Dial.zerosDuring (d: Dial highest): Turn -> Nat
  | Right n => (d.position + n) / d.size
  | Left n  => ((d.size - d.position) % d.size + n) / d.size

def zerosFrom (x: Int) (t: Turn): Nat := (Dial.fromInt 99 x).zerosDuring t

test "left past zero" := zerosFrom 10 (Left 40) == 1
test "left onto zero" := zerosFrom 20 (Left 20) == 1
test "right onto zero" := zerosFrom 0 (Right 100) == 1
test "left from zero" := zerosFrom 0 (Left 42) == 0
test "left a full turn from zero" := zerosFrom 0 (Left 200) == 2
