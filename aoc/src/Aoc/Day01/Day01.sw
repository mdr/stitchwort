-- Advent of Code 2025, day 1: a dial numbered 0 to 99 starts at 50 and is
-- turned left or right. Part 1 counts the turns that end on 0; part 2 counts
-- every click that lands on 0, including those in the middle of a turn.
--
--   $ cd aoc && stitchwort run Aoc.Day01.main < inputs/day01.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- The dial is a `Mod n`, a number below `n` that wraps around (`Mod 100` in
-- the puzzle). Part 2 is proved correct, for a dial of any size, in
-- `Aoc.Day01.Proofs` (Proofs/Part2.sw), and the tests are in `Aoc.Day01.Tests`
-- (Tests/); `run` checks neither.

namespace Aoc.Day01
import Std (IO, Int, List, Mod)

def main(): {IO} () :=
  let turns := parseTurns (IO.readAllLines())
  IO.print "Part 1: ${solvePart1 turns}"
  IO.print "Part 2: ${solvePart2 turns}"

def parseTurns (lines: List Text): List Turn := lines.filterMap Turn.parse

def solvePart1 (turns: List Turn): Nat := zerosLandedOn dial turns

def solvePart2 (turns: List Turn): Nat := zerosPassed dial turns

-- The puzzle's dial: 100 positions, 0 to 99, at 50.
def dial: Mod 100 := Mod.ofNat 50

-- Part 1: the positions after each turn that are 0.
def zerosLandedOn (start: Mod n) (turns: List Turn): Nat :=
  turns
    |> .scanLeft move start
    |> .drop 1
    |> .count isZero

-- Part 2: for each turn, the clicks onto 0 from where the dial was before it.
def zerosPassed (start: Mod n) (turns: List Turn): Nat :=
  turns
    |> .scanLeft move start
    |> .zipWith zerosDuring turns
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

-- A turn, one click at a time: `Left 3` is three `Left 1`s. Only the
-- specification of part 2 and its proofs (`Aoc.Day01.Proofs`) use it; it stays
-- here so that they can write `t.clicks`, a dot name must live with its type.
def Turn.clicks: Turn -> List Turn
  | Left n  => List.replicate n (Left 1)
  | Right n => List.replicate n (Right 1)

-- Where a turn leaves the dial: left is towards lower numbers.
def move (d: Mod n): Turn -> Mod n
  | Left k  => Mod.ofInt (d.toInt - k.toInt)
  | Right k => Mod.ofInt (d.toInt + k.toInt)

def isZero (d: Mod n): Bool := d.value == 0

-- How many clicks of a turn land on 0. Going right from `d`, the dial is at
-- 0 after each click that brings `d + k` to a multiple of the dial's size.
-- Going left is the mirror image: 0 is `(size - d) % size` clicks away.
def zerosDuring [n: Nat] (d: Mod n): Turn -> Nat
  | Right k => (d.value + k) / Mod.size n
  | Left k  => ((Mod.size n - d.value) % Mod.size n + k) / Mod.size n
