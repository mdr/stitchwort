-- Advent of Code 2025, day 1: a dial numbered 0 to 99 starts at 50 and is
-- turned left or right. Part 1 counts the turns that end on 0; part 2 counts
-- every click that lands on 0, including those in the middle of a turn.
--
--   $ cd aoc && stitchwort run Aoc.Day01.main < inputs/day01.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- The dial is a record around a `Mod n`, a number below `n` that wraps around
-- (`Mod 100` in the puzzle), so the program reads `dial.move turn` and
-- `dial.isZero`. Part 2 is proved correct, for a dial of any size, in
-- `Aoc.Day01.Proofs` (Proofs/Part2.sw), and the tests are in `Aoc.Day01.Tests`
-- (Tests/); `run` checks neither.

namespace Aoc.Day01
import Aoc.Common (parseLines)
import Std (Fail, IO, Int, List, Mod)
import Std.Fail (fail, need)

def main(): {IO, Fail} () :=
  let turns := parseTurns IO.readAllLines()
  IO.print "Part 1: ${solvePart1 turns}"
  IO.print "Part 2: ${solvePart2 turns}"

-- One turn per line. Spaces around a turn are allowed; anything else fails,
-- naming the line.
def parseTurns (lines: List Text): {Fail} (List Turn) := parseLines Turn.parse lines

def solvePart1 (turns: List Turn): Nat := zerosLandedOn startingDial turns

def solvePart2 (turns: List Turn): Nat := zerosPassed startingDial turns

-- The dial: where it points, on a dial of `n` positions.
type Dial (n: Nat) = { position: Mod n }

-- The puzzle's dial: 100 positions, 0 to 99, at 50.
def startingDial: Dial 100 := { position = Mod.ofNat 50 }

-- Part 1: the positions after each turn that are 0.
def zerosLandedOn (startingDial: Dial n) (turns: List Turn): Nat :=
  turns
    |> .scanLeft startingDial .move
    |> .drop 1
    |> .count .isZero

-- Part 2: for each turn, the clicks onto 0 from where the dial was before it.
def zerosPassed (startingDial: Dial n) (turns: List Turn): Nat :=
  turns
    |> .scanLeft startingDial .move
    |> .zipWith turns .zerosDuring
    |> .sum

type Turn =
  | Left (distance: Nat)
  | Right (distance: Nat)

-- "L68" is `Left 68`; " R5 " is `Right 5`.
def Turn.parse (line: Text): {Fail} Turn :=
  match line.trim.uncons with
    | Some ('L', rest) => Left (need rest.toNat "expected a turn like L68, got '${line}'")
    | Some ('R', rest) => Right (need rest.toNat "expected a turn like L68, got '${line}'")
    | _ => fail "expected a turn like L68, got '${line}'"

def Turn.parseOption (line: Text): Option Turn := Fail.toOption (() => Turn.parse line)

-- A turn, one click at a time: `Left 3` is three `Left 1`s. Only the
-- specification of part 2 and its proofs (`Aoc.Day01.Proofs`) use it; it stays
-- here so that they can write `turn.clicks`, a dot name must live with its type.
def Turn.clicks: Turn -> List Turn
  | Left distance => List.replicate distance (Left 1)
  | Right distance => List.replicate distance (Right 1)

-- Where a turn leaves the dial: left is towards lower numbers.
def Dial.move (dial: Dial n): Turn -> Dial n
  | Left distance => { position = dial.position.subNat distance }
  | Right distance => { position = dial.position.addNat distance }

def Dial.isZero (dial: Dial n): Bool := dial.position.isZero

-- How many clicks of a turn land on 0. Going right from `dial`, the dial is at
-- 0 after each click that brings `dial + k` to a multiple of the dial's size.
-- Going left is the mirror image: turning left from `dial` is turning right
-- from `(size - dial) % size`, the dial's position in a mirror, where the
-- number 0 stays put and the others swap ends (20 becomes 80 on a dial of
-- 100). That mirrored position is not the distance to 0 going left (from 20
-- that is 20 clicks, not 80); it is the position to count right-turns from.
def Dial.zerosDuring [n: Nat] (dial: Dial n): Turn -> Nat
  | Right distance => (dial.position.value + distance) / Mod.size n
  | Left distance => ((Mod.size n - dial.position.value) % Mod.size n + distance) / Mod.size n
