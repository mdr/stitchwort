--| Day 3 as the puzzle states it: each bit of a rate, and each step of the
--| filtering, looks at one position of the numbers, counted from the left.
--| The proofs (Proofs/) show the program computes the same answers, for
--| every list of numbers.
--|
--| Three things the puzzle leaves open are decided here:
--|
--| - Ties. Part 2 says a tie keeps 1s for the oxygen generator rating and 0s
--|   for the CO2 scrubber rating. Part 1 says nothing (its inputs have no
--|   ties); it is read the same way, so a tie's most common bit is 1 and its
--|   least common bit is 0.
--| - A bit no number has. "The least common value" counts both values, so in
--|   a position where every number left has a 1, the least common value is
--|   0, and keeping the numbers with a 0 there keeps none. Then no number is
--|   left, the filtering never stops at one, and there is no rating.
--| - The end. "If you only have one number left, stop", and otherwise go on
--|   to the next bit to the right. When there is no next bit (more than one
--|   number is still left, so some are the same), or no number is left, the
--|   puzzle has no rating, and nor does the spec: the ratings are `Option`s.
--|
--| The numbers all have the same number of bits in the puzzle; the spec reads
--| that many positions off the first. A number too short to have a bit at a
--| position counts as neither a 0 nor a 1 there (the parser rejects such
--| input, but the spec is defined for it).

namespace Aoc.Year2021.Day03.Spec
import Aoc.Common (Bits)
import Std (List, Nat)

--| How many bits each number has: the first number's.
def width (report: List Bits): Nat := (report.headOr Bits.empty).width

--| How many of the numbers have `bit` at `position`.
def howMany (numbers: List Bits) (position: Nat) (bit: Bool): Nat :=
  numbers.count (number => number.get position == Some bit)

--| The most common bit at `position`: 1, unless there are more 0s than 1s.
def mostCommonAt (numbers: List Bits) (position: Nat): Bool :=
  howMany numbers position False ≤ howMany numbers position True

--| The least common bit at `position`: 0, unless there are fewer 1s than 0s.
def leastCommonAt (numbers: List Bits) (position: Nat): Bool :=
  howMany numbers position True < howMany numbers position False

--| Part 1: "each bit in the gamma rate can be determined by finding the most
--| common bit in the corresponding position of all numbers", and the epsilon
--| rate likewise from the least common bit. Each is read as a binary number.
def gamma (report: List Bits): Bits := { bits = List.range (width report) |> .map (mostCommonAt report) }

def epsilon (report: List Bits): Bits := { bits = List.range (width report) |> .map (leastCommonAt report) }

def gammaRate (report: List Bits): Nat := (gamma report).value

def epsilonRate (report: List Bits): Nat := (epsilon report).value

--| The power consumption: the gamma rate times the epsilon rate.
def powerConsumption (report: List Bits): Nat := gammaRate report * epsilonRate report

--| Part 2: "keep only numbers with that bit in that position".
def keep (numbers: List Bits) (position: Nat) (bit: Bool): List Bits :=
  numbers.filter (number => number.get position == Some bit)

--| Considering the positions in turn: "if you only have one number left,
--| stop", it is the rating; otherwise keep the numbers with the bit the
--| criterion picks at this position, and go on to the next bit to the right.
def findRating (criterion: List Bits → Nat → Bool): List Bits → (positions: List Nat) → Option Bits
  | [number], _ => Some number
  | numbers, [] => None
  | numbers, [position, ..later] => findRating criterion (keep numbers position (criterion numbers position)) later

--| The oxygen generator rating keeps the most common bits, the CO2 scrubber
--| rating the least common; each starts from the whole report at the first
--| bit.
def oxygenGeneratorRating (report: List Bits): Option Nat :=
  findRating mostCommonAt report (List.range (width report)) |> .map Bits.value

def co2ScrubberRating (report: List Bits): Option Nat :=
  findRating leastCommonAt report (List.range (width report)) |> .map Bits.value

--| The life support rating: the oxygen generator rating times the CO2
--| scrubber rating, when both exist.
def lifeSupportRating (report: List Bits): Option Nat :=
  (oxygenGeneratorRating report, co2ScrubberRating report)
    |> match some | (Some oxygen, Some carbonDioxide) => oxygen * carbonDioxide
