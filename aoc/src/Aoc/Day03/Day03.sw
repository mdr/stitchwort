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
import Std (Char, IO, Nat)

def main(): {IO} () :=
  let banks := parseBanks (IO.readAllLines())
  IO.print "Part 1: ${solvePart1 banks}"
  IO.print "Part 2: ${solvePart2 banks}"

def parseBanks (lines: List Text): List Bank := lines.map Bank.parse

def solvePart1 (banks: List Bank): Nat := total 2 banks

def solvePart2 (banks: List Bank): Nat := total 12 banks

def total (k: Nat) (banks: List Bank): Nat := banks |> .sumBy (joltage k)

def joltage (k: Nat) (bank: Bank): Nat := bank |> .best k |> Nat.fromDigits

-- A bank of batteries: one digit per battery.
def Bank: Type := List Nat

def Bank.parse (t: Text): Bank := t.toList |> .filterMap Char.digitValue

-- The digits of the largest k-digit number that is a subsequence of ds.
def Bank.best: Nat -> Bank -> Bank
  | Zero,   _           => []
  | Succ _, []          => []
  | Succ k, Cons d rest =>
    -- The leftmost largest of the next w digits, and what follows it. The
    -- candidate so far is c, followed by `after`.
    def pick: Nat -> List Nat -> Nat -> List Nat -> (Nat, List Nat)
      | Zero,   _,           c, after => (c, after)
      | Succ _, [],          c, after => (c, after)
      | Succ w, Cons x more, c, after =>
        if c < x then pick w more x more else pick w more c after
    let (top, after) := pick (rest.length - k) rest d rest
    Cons top (Bank.best k after)
