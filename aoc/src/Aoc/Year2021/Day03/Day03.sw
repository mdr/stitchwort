--| Advent of Code 2021, day 3: a submarine's diagnostic report is a list of
--| binary numbers, one per line, all with the same number of bits. Part 1
--| reads two numbers off the report's columns: the gamma rate takes each
--| column's most common bit, the epsilon rate its least common; the answer is
--| their product. Part 2 finds two numbers in the report by filtering it one
--| column at a time, keeping the numbers with the column's most common bit
--| (the oxygen generator rating) or its least common bit (the CO2 scrubber
--| rating), until one number is left; the answer is their product.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day03.main < inputs/2021/day03.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| Part 1 finds only the gamma rate: the least common bit of a column is the
--| one the most common bit isn't, so the epsilon rate is the gamma rate with
--| every bit flipped, which is 2^width - 1 less the gamma rate. Part 2 doesn't
--| look a column up in every number: it keeps, of each number that has the
--| chosen bit first, the bits after it, and goes on with those, so the next
--| column is always the first. The proofs that both answers are the puzzle's,
--| for every list of numbers, are in `Aoc.Year2021.Day03.Proofs` (Proofs/),
--| and the tests in `Aoc.Year2021.Day03.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day03
import Std (Fail, IO, List, Nat, Parse)
import Std.Parse (label, many1, pick)

def main(): {IO, Fail} () :=
  let numbers := parseReport IO.readAll()
  IO.print "Part 1: ${solvePart1 numbers}"
  IO.print "Part 2: ${solvePart2 numbers |> .orFail "the filtering didn't end with one number"}"

--| A number is its bits, the most significant first; `True` is a 1.
type Bits = List Bool

--| One number per line. A line that isn't all 0s and 1s fails, naming the
--| line and column, and so does a number with a different number of bits
--| from the first.
def parseReport (input: Text): {Fail} List Bits :=
  let numbers := Parse.eachLine input (() => many1 bit)
  let width := (numbers.headOr []).length
  match numbers.withIndex.find (((_, number)) => number.length != width) with
    | Some (index, number) => Fail.fail "line ${index + 1}: ${number.length} bits, but the first line has ${width}"
    | None => numbers

def bit(): {Parse} Bool := label "0 or 1" (() => pick [("0", False), ("1", True)])

--| A column's most common bit: 1 when at least half of the bits are 1s, so a
--| tie is 1.
def mostCommon (column: List Bool): Bool := column.length ≤ 2 * column.count (bit => bit)

--| Part 1: the gamma rate times the epsilon rate, which is the gamma rate's
--| bits flipped.
def solvePart1 (numbers: List Bits): Nat :=
  let gamma: Bits := numbers.transpose |> .map mostCommon
  Nat.fromBits gamma * (Nat.pow 2 gamma.length - 1 - Nat.fromBits gamma)

--| The bits after the first, of a number whose first bit is `bit`.
def afterBit (bit: Bool): Bits → Option Bits
  | [] => None
  | [first, ..rest] => if first == bit then Some rest else None

--| The rating found from `numbers`, with `columns` columns left to filter on:
--| the bits it starts with are chosen by `choose` from the numbers' first
--| bits. `None` when no column is left and more or less than one number is.
def rating (choose: List Bool → Bool): (columns: Nat) → List Bits → Option Bits
  | _, [number] => Some number
  | Zero, _ => None
  | Succ later, numbers =>
    let bit := choose (numbers.filterMap .head)
    rating choose later (numbers.filterMap (afterBit bit)) |> .map (Cons bit)

--| Part 2: the oxygen generator rating, from the most common bits, times the
--| CO2 scrubber rating, from the least common.
def solvePart2 (numbers: List Bits): Option Nat :=
  let width := (numbers.headOr []).length
  let oxygen := rating mostCommon width numbers
  let carbonDioxide := rating (column => not (mostCommon column)) width numbers
  oxygen.flatMap (o => carbonDioxide.map (c => Nat.fromBits o * Nat.fromBits c))
