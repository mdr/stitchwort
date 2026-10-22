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
import Std (IO, Int, List, Mod)

def main(): {IO} () :=
  let turns := parseTurns IO.readAllLines()
  IO.print "Part 1: ${solvePart1 turns}"
  IO.print "Part 2: ${solvePart2 turns}"

def parseTurns (lines: List Text): List Turn := lines.filterMap Turn.parse

def solvePart1 (turns: List Turn): Nat := zerosLandedOn startingDial turns

def solvePart2 (turns: List Turn): Nat := zerosPassed startingDial turns

-- The dial: where it points, on a dial of `n` positions.
type Dial (n: Nat) = { position: Mod n }

-- The puzzle's dial: 100 positions, 0 to 99, at 50.
def startingDial: Dial 100 := { position = Mod.ofNat 50 }

-- Part 1: the positions after each turn that are 0.
def zerosLandedOn (startingDial: Dial n) (turns: List Turn): Nat :=
  turns
    |> .scanLeft Dial.move startingDial
    |> .drop 1
    |> .count Dial.isZero

-- Part 2: for each turn, the clicks onto 0 from where the dial was before it.
def zerosPassed (startingDial: Dial n) (turns: List Turn): Nat :=
  turns
    |> .scanLeft Dial.move startingDial
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

-- A turn, one click at a time: `Left 3` is three `Left 1`s. Only the
-- specification of part 2 and its proofs (`Aoc.Day01.Proofs`) use it; it stays
-- here so that they can write `t.clicks`, a dot name must live with its type.
def Turn.clicks: Turn -> List Turn
  | Left n  => List.replicate n (Left 1)
  | Right n => List.replicate n (Right 1)

-- Where a turn leaves the dial: left is towards lower numbers.
def Dial.move (dial: Dial n): Turn -> Dial n
  | Left k  => { position = dial.position.subNat k }
  | Right k => { position = dial.position.addNat k }

def Dial.isZero (dial: Dial n): Bool := dial.position.isZero

-- How many clicks of a turn land on 0. Going right from `dial`, the dial is at
-- 0 after each click that brings `dial + k` to a multiple of the dial's size.
-- Going left is the mirror image: 0 is `(size - dial) % size` clicks away.
def Dial.zerosDuring [n: Nat] (dial: Dial n): Turn -> Nat
  | Right k => (dial.position.value + k) / Mod.size n
  | Left k  => ((Mod.size n - dial.position.value) % Mod.size n + k) / Mod.size n
