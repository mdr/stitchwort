-- Day 11 as the puzzle states it: a line of stones, every one changing at
-- each blink, the order kept. The proofs (Proofs/) show the program counts
-- these stones, for every line and every number of blinks.

namespace Aoc.Year2024.Day11.Spec
import Std (List, Nat)

-- "Every time you blink, the stones each simultaneously change according to
-- the first applicable rule in this list":
--
-- "If the stone is engraved with the number 0, it is replaced by a stone
-- engraved with the number 1."
--
-- "If the stone is engraved with a number that has an even number of digits,
-- it is replaced by two stones. The left half of the digits are engraved on
-- the new left stone, and the right half of the digits are engraved on the
-- new right stone. (The new numbers don't keep extra leading zeroes: 1000
-- would become stones 10 and 0.)"
--
-- "If none of the other rules apply, the stone is replaced by a new stone;
-- the old stone's number multiplied by 2024 is engraved on the new stone."
def change (stone: Nat): List Nat :=
  let digits := Nat.digits stone
  let half := digits.length / 2
  if stone == 0 then [1]
  else if digits.length % 2 == 0 then [Nat.fromDigits (digits.take half), Nat.fromDigits (digits.drop half)]
  else [stone * 2024]

-- "No matter how the stones change, their order is preserved, and they stay
-- on their perfectly straight line."
def blink (stones: List Nat): List Nat := stones.flatMap change

-- The line after `blinks` blinks.
def blinkTimes (blinks: Nat) (stones: List Nat): List Nat := blinks.iterate blink stones

-- "How many stones will you have after blinking 25 times?"
def part1 (stones: List Nat): Nat := (blinkTimes 25 stones).length

-- "How many stones would you have after blinking a total of 75 times?"
def part2 (stones: List Nat): Nat := (blinkTimes 75 stones).length
