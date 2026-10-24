-- Advent of Code 2025, day 3: each line is a bank of batteries with a digit
-- on each. Pick k batteries, in order, to make the largest k-digit number
-- (2 digits in part 1, 12 in part 2). Sum the best number over the banks.
--
--   $ cd aoc && stitchwort run Aoc.Day03.main < inputs/day03.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- Greedy: the first digit is the largest one in the part of the bank that
-- still leaves k - 1 digits after it, taking the leftmost such digit so the
-- most is left over; then repeat on what follows it.
--
-- That this is the largest number is proved in `Aoc.Day03.Proofs`
-- (Proofs/Best.sw); the tests are in `Aoc.Day03.Tests` (Tests/). `run` checks
-- neither.

namespace Aoc.Day03
import Aoc.Common (parseLines)
import Std (Char, Fail, Fin, IO, Nat)
import Std.Fail (fail, need)

def main(): {IO, Fail} () :=
  let banks := parseBanks IO.readAllLines()
  IO.print "Part 1: ${solvePart1 banks}"
  IO.print "Part 2: ${solvePart2 banks}"

-- One bank per line. Spaces around a bank are allowed; anything else fails,
-- naming the line.
def parseBanks (lines: List Text): {Fail} (List Bank) := parseLines Bank.parse lines

def solvePart1 (banks: List Bank): Nat := banks |> .sumBy (maxJoltage 2)

def solvePart2 (banks: List Bank): Nat := banks |> .sumBy (maxJoltage part2Batteries)

-- Part 2 turns on exactly this many batteries of each bank.
def part2Batteries: Nat := 12

-- The joltage of some batteries turned on: the number their digits spell, in order.
def joltageOf (on: List Battery): Nat := Nat.fromDigits (on.map .toNat)

-- The most joltage from turning on count batteries of the bank, or all of them if the bank has fewer.
def maxJoltage (count: Nat) (bank: Bank): Nat := joltageOf (bank.best count)

-- A battery, labelled with its joltage rating, a digit.
def Battery: Type := Fin 10

-- A bank of batteries: a digit on each.
def Bank: Type := List Battery

-- A row of digits is a bank of that many batteries. A bank must have the
-- `part2Batteries` that part 2 turns on (and so the 2 of part 1), so the
-- program only runs on banks the headline theorem covers (`enough` in
-- Proofs/Best.sw). A shorter one is an input error.
def Bank.parse (line: Text): {Fail} Bank :=
  let msg := "expected a row of digits, got '${line}'"
  match line.trim.toList with
    | Nil => fail msg
    | chars =>
      let bank := chars |> .map (char => need char.toDigit msg)
      if bank.length < part2Batteries then fail "expected at least ${part2Batteries} batteries, got ${bank.length}" else bank

-- The digits of the largest number of `count` digits that is a subsequence of the bank (`count` is the first argument; all the digits if the bank has fewer).
def Bank.best: Nat -> Bank -> Bank
  | Zero, _ => []
  | Succ _, [] => []
  | Succ remaining, Cons first rest =>
    -- The leftmost largest of the next `window` digits, and what follows it. The
    -- candidate so far is `candidate`, followed by `after`.
    def pick: Nat -> Bank -> Fin 10 -> Bank -> (Fin 10, Bank)
      | Zero, _, candidate, after => (candidate, after)
      | Succ _, [], candidate, after => (candidate, after)
      | Succ window, Cons x more, candidate, after =>
        if candidate < x then pick window more x more else pick window more candidate after
    let (top, after) := pick (rest.length - remaining) rest first rest
    Cons top (Bank.best remaining after)
