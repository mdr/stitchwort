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
-- (Proofs/Best.sw), which `run` does not check.

namespace Aoc.Day03

def main(): {IO} () :=
  let banks := parseBanks (IO.readAllLines())
  IO.print "Part 1: ${solvePart1 banks}"
  IO.print "Part 2: ${solvePart2 banks}"

def parseBanks (lines: List Text): List Bank := lines.map Bank.parse

def solvePart1 (banks: List Bank): Nat := total 2 banks

def solvePart2 (banks: List Bank): Nat := total 12 banks

def total (k: Nat) (banks: List Bank): Nat := banks |> .sumBy (joltage k)

def joltage (k: Nat) (bank: Bank): Nat := bank |> .best k |> Nat.fromDigits

def example: List Text := ["987654321111111", "811111111111119", "234234234234278", "818181911112111"]

test "example" := (solvePart1 (parseBanks example), solvePart2 (parseBanks example)) == (357, 3121910778619)
test "banks part 1" := (parseBanks example).map (joltage 2) == [98, 89, 78, 92]
test "banks part 2" := (parseBanks example).map (joltage 12) == [987654321111, 811111111119, 434234234278, 888911112111]

-- A bank of batteries: one digit per battery.
def Bank: Type := List Nat

def Bank.parse (t: Text): Bank := t.toList |> .filterMap Char.digitValue

test "parse" := Bank.parse "102" == [1, 0, 2]

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

test "zeros" := Bank.best 2 [0, 0, 5, 0] == [5, 0]
test "leftmost wins" := Bank.best 1 [3, 9, 9, 1] == [9]
test "keep everything" := Bank.best 3 [4, 5, 6] == [4, 5, 6]
test "too short" := Bank.best 5 [1, 2] == [1, 2]
test "pick none" := Bank.best 0 [1, 2, 3] == []
