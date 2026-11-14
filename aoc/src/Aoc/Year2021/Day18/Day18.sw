--| Advent of Code 2021, day 18: snailfish numbers are pairs whose two
--| elements are regular numbers or snailfish numbers. Adding two makes the
--| pair of them and then reduces it: while some pair is nested inside four
--| pairs the leftmost such explodes (its values go to the nearest regular
--| numbers on each side, and it becomes 0); otherwise, while some regular
--| number is 10 or more, the leftmost such splits into a pair of its halves.
--| A number's magnitude is 3 times its left's plus 2 times its right's.
--| Part 1 adds the input's numbers in order and gives the magnitude of the
--| total; part 2 the largest magnitude of the sum of two different lines.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day18.main < inputs/2021/day18.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| The program works on the tree. An explosion is found by walking down to
--| the pair, and the values it throws out are handed back up until a
--| subtree on the right side can take them (`Explosion`). Reduction has a
--| step budget (`steps`), so a sum is an `Option`; no sum of the puzzle's
--| needs more than a few dozen steps. The proofs (Proofs/) show that each
--| explode and split step is the spec's step on the numbers' leaves in
--| reading order, that a finished sum is reduced, and that the answers are
--| the spec's. The tests are in `Aoc.Year2021.Day18.Tests` (Tests/). `run`
--| checks neither.

namespace Aoc.Year2021.Day18
import Std (Fail, IO, List, Nat, Option, Parse, Text)
import Std.Parse (char, nat)

def main(): {IO, Fail} () :=
  let numbers := parseNumbers IO.readAll()
  IO.print "Part 1: ${solvePart1 numbers |> .orFail "no numbers to add"}"
  IO.print "Part 2: ${solvePart2 numbers |> .orFail "fewer than two numbers"}"

type Number = | Regular (value: Nat) | Pair (left: Number) (right: Number)

--| What an explosion inside a number leaves: the exploded pair's left value
--| if no regular number in this number was left of it to take it (else 0),
--| the number with the pair replaced by 0, and likewise the right value.
type Explosion = { toLeft: Nat, number: Number, toRight: Nat }

def addLeftmost (amount: Nat): Number → Number
  | Regular value => Regular (value + amount)
  | Pair left right => Pair (addLeftmost amount left) right

def addRightmost (amount: Nat): Number → Number
  | Regular value => Regular (value + amount)
  | Pair left right => Pair left (addRightmost amount right)

--| The leftmost pair of two regular numbers nested inside at least four
--| pairs, exploded; `depth` is how many pairs the number is inside.
def explode (depth: Nat): Number → Option Explosion
  | Regular _ => None
  | Pair (Regular a) (Regular b) => if 4 ≤ depth then Some { toLeft = a, number = Regular 0, toRight = b } else None
  | Pair left right =>
    match explode (depth + 1) left with
      | Some inLeft =>
        Some { toLeft = inLeft.toLeft, number = Pair inLeft.number (addLeftmost inLeft.toRight right), toRight = 0 }
      | None =>
        match explode (depth + 1) right with
          | Some inRight =>
            Some {
              toLeft = 0,
              number = Pair (addRightmost inRight.toLeft left) inRight.number,
              toRight = inRight.toRight
            }
          | None => None

--| The leftmost regular number of 10 or more, split into its halves (the
--| left rounded down, the right up).
def split: Number → Option Number
  | Regular value => if 10 ≤ value then Some (Pair (Regular (value / 2)) (Regular ((value + 1) / 2))) else None
  | Pair left right =>
    match split left with
      | Some left2 => Some (Pair left2 right)
      | None =>
        match split right with
          | Some right2 => Some (Pair left right2)
          | None => None

--| Explode while something can, else split, until neither can; `None` if
--| that takes more than `budget` steps.
def reduce: Nat → Number → Option Number
  | 0, _ => None
  | Succ budget, number =>
    match explode 0 number with
      | Some exploded => reduce budget exploded.number
      | None =>
        match split number with
          | Some split2 => reduce budget split2
          | None => Some number

--| Far more steps than any sum of the puzzle's takes.
def steps: Nat := 1000

def add (x y: Number): Option Number := reduce steps (Pair x y)

def magnitude: Number → Nat
  | Regular value => value
  | Pair left right => 3 * magnitude left + 2 * magnitude right

--| `total` with each of `numbers` added to it in turn.
def addAll (total: Number): List Number → Option Number
  | [] => Some total
  | [next, ..rest] =>
    match add total next with
      | Some sum => addAll sum rest
      | None => None

def solvePart1: List Number → Option Nat
  | [] => None
  | [first, ..rest] => (addAll first rest).map magnitude

--| Every ordered pair of numbers on different lines.
def orderedPairs (numbers: List Number): List (Number, Number) :=
  numbers.withIndex |> .flatMap (((i, x)) => numbers.withIndex |> .filterMap (match some | (j, y) if i != j => (x, y)))

--| The magnitude of each pair's sum, or `None` if a sum runs out of steps.
def sumMagnitudes: List (Number, Number) → Option (List Nat)
  | [] => Some []
  | [(x, y), ..rest] =>
    match add x y, sumMagnitudes rest with
      | Some sum, Some others => Some [magnitude sum, ..others]
      | _, _ => None

def solvePart2 (numbers: List Number): Option Nat := match sumMagnitudes (orderedPairs numbers) with
  | Some magnitudes => magnitudes.maximum
  | None => None

--| One number per line. Fails unless each is already reduced, as the
--| puzzle's are: no pair inside four pairs, no regular number above 9.
def parseNumbers (input: Text): {Fail} List Number := checkNumbers (readNumbers input)

def readNumbers (input: Text): {Fail} List Number :=
  input.trim.lines.map (line => Parse.line line (() => number line.length))

--| A regular number or a pair; `room` bounds the nesting, and
--| a line of `n` characters can't nest deeper than `n`.
def number: Nat → {Parse} Number
  | 0 => Regular (nat())
  | Succ room => Parse.oneOf [
    () => Regular (nat()),
    () =>
      char '['
      let left := number room
      char ','
      let right := number room
      char ']'
      Pair left right
  ]

def checkNumbers (numbers: List Number): {Fail} List Number := match firstUnreduced numbers with
  | Some line => Fail.fail "line ${line + 1} isn't a reduced snailfish number"
  | None => numbers

--| The index of the first number that isn't reduced.
def firstUnreduced (numbers: List Number): Option Nat := numbers.findIndex (x => not (reduced 0 x))

--| No pair inside four pairs and no regular number above 9, for a number
--| inside `depth` pairs.
def reduced (depth: Nat): Number → Bool
  | Regular value => value ≤ 9
  | Pair left right => depth < 4 ∧ reduced (depth + 1) left ∧ reduced (depth + 1) right
