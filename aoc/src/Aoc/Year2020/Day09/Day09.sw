--| Advent of Code 2020, day 9: XMAS-encrypted data, one number a line. After
--| a preamble (25 numbers in the puzzle, 5 in its example), each number
--| should be the sum of two different numbers among the preamble's worth
--| just before it. Part 1 is the first number that isn't; part 2 finds a
--| contiguous run of at least two numbers summing to it, and adds the run's
--| smallest and largest: the encryption weakness.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day09.main < inputs/2020/day09.txt
--|
--| Part 1 walks the data once, checking each number against a set of the
--| numbers before it. Part 2 slides a window along the data in one pass,
--| growing it at the back while its sum is below the target and shrinking
--| it at the front while above, so each number joins and leaves it at most
--| once. The proofs, that the parser reads one number a line and that both
--| answers are the puzzle's, are in `Aoc.Year2020.Day09.Proofs` (Proofs/),
--| and the tests in `Aoc.Year2020.Day09.Tests` (Tests/); `run` checks
--| neither.

namespace Aoc.Year2020.Day09
import Std (Fail, IO, List, NonEmptyList, Option, Parse, Set)

def main(): {IO, Fail} () :=
  let data := parseData IO.readAll()
  let invalid := data.firstInvalid (preamble := 25) |> .orFail "every number is the sum of two before it"
  IO.print "Part 1: ${invalid}"
  IO.print "Part 2: ${data.weakness invalid |> .orFail "no run of two or more numbers sums to ${invalid}"}"

--| The numbers as received, in order.
type XmasData = { numbers: List Nat }

def parseData (input: Text): {Fail} XmasData := { numbers = Parse.eachLine input Parse.nat }

--| The numbers just before one, which it should be the sum of two of.
type Window = { numbers: List Nat }

--| Whether `number` is the sum of two numbers of the window with different
--| values: some `a` whose partner `number - a` is in the window too.
def Window.sumsTo (window: Window) (number: Nat): Bool :=
  let present := window.numbers.toSet
  window.numbers.any (a => a <= number && a + a != number && present.contains (number - a))

--| The first number of `front.drop preamble` that its `preamble` numbers
--| before it don't sum to.
def firstInvalidFrom (preamble: Nat) (front: List Nat): Option Nat := match front.drop preamble with
  | [] => None
  | [number, .._] =>
    if ({ numbers = front.take preamble }: Window).sumsTo number then
      match front with
        | [] => None
        | [_, ..rest] => firstInvalidFrom preamble rest
    else Some number

--| Part 1: the first number after the preamble that isn't the sum of two
--| different numbers among the `preamble` before it.
def XmasData.firstInvalid (data: XmasData) (preamble: Nat): Option Nat := firstInvalidFrom preamble data.numbers

--| A window sliding along the numbers: the `count` numbers at the start of
--| `front`, summing to `sum`, followed by `rest` (`front.drop count`).
--| It grows by taking from `rest` and shrinks by dropping from `front`;
--| each step does one or the other, so the run ends.
def runFrom (target: Nat) (front: List Nat) (count sum: Nat) (rest: List Nat): Option (List Nat)
    decreasing front.length + rest.length
:=
  if target < sum then
    match front with
      | [] => None
      | [first, ..later] => runFrom target later (count - 1) (sum - first) rest
  else if sum == target && 2 <= count then Some (front.take count)
  else
    match rest with
      | [] => None
      | [next, ..more] => runFrom target front (count + 1) (sum + next) more

--| A contiguous run of at least two numbers summing to `target`: for each
--| end, the window is the longest run ending there whose sum is at most
--| `target`, so any run summing to it is found.
def XmasData.runSumming (data: XmasData) (target: Nat): Option (List Nat) :=
  runFrom target data.numbers 0 0 data.numbers

--| Part 2: the smallest plus the largest number of a contiguous run of at
--| least two numbers summing to `invalid`.
def XmasData.weakness (data: XmasData) (invalid: Nat): Option Nat :=
  data.runSumming invalid |> .flatMap List.nonEmpty |> .map (run => run.minimum + run.maximum)
