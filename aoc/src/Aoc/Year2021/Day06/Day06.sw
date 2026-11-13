--| Advent of Code 2021, day 6: a school of lanternfish. Each fish has a
--| timer, the number of days until it next spawns. Every day each timer
--| goes down by one, except that a fish at 0 goes back to 6 and spawns a
--| new fish whose timer starts at 8. The input is the timers, separated by
--| commas. Part 1 counts the fish after 80 days, part 2 after 256.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day06.main < inputs/2021/day06.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| After 256 days there are over a trillion fish, too many to list, but fish
--| with the same timer behave alike, so the program only counts the fish at
--| each timer, 0 to 8, and moves the counts along a day at a time. The proof
--| that this counts the fish the puzzle's day-by-day list of every fish has,
--| for every input and every number of days, is in
--| `Aoc.Year2021.Day06.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2021.Day06.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day06
import Std (Fail, IO, List, Nat, Parse)
import Std.Parse (char, nat, sepBy1)

def main(): {IO, Fail} () :=
  let timers := parseTimers IO.readAll()
  IO.print "Part 1: ${solvePart1 timers}"
  IO.print "Part 2: ${solvePart2 timers}"

--| The timers on one line, separated by commas. A timer above 8 fails,
--| naming its place: no fish's timer starts above 8.
def parseTimers (input: Text): {Fail} List Nat := checkTimers (Parse.line input (() => sepBy1 nat (() => char ',') |> .toList))

--| The timers, if none is above 8; otherwise fail, naming the first that is.
def checkTimers (timers: List Nat): {Fail} List Nat := match firstAbove8 timers with
  | Some (index, _) => Fail.fail "timer ${index + 1} is above 8"
  | None => timers

--| The first timer above 8, with its index.
def firstAbove8 (timers: List Nat): Option (Nat, Nat) := timers.withIndex.find (((_, timer)) => 8 < timer)

--| How many fish have each timer, `t0` the fish at 0 to `t8` those at 8.
type Counts = { t0: Nat, t1: Nat, t2: Nat, t3: Nat, t4: Nat, t5: Nat, t6: Nat, t7: Nat, t8: Nat }

def Counts.ofTimers (timers: List Nat): Counts := {
  t0 = timers.count (== 0),
  t1 = timers.count (== 1),
  t2 = timers.count (== 2),
  t3 = timers.count (== 3),
  t4 = timers.count (== 4),
  t5 = timers.count (== 5),
  t6 = timers.count (== 6),
  t7 = timers.count (== 7),
  t8 = timers.count (== 8)
}

--| A day: every count moves down a timer; the fish at 0 go to 6, and as
--| many new fish start at 8.
def Counts.nextDay (counts: Counts): Counts := {
  t0 = counts.t1,
  t1 = counts.t2,
  t2 = counts.t3,
  t3 = counts.t4,
  t4 = counts.t5,
  t5 = counts.t6,
  t6 = counts.t7 + counts.t0,
  t7 = counts.t8,
  t8 = counts.t0
}

def Counts.total (counts: Counts): Nat :=
  counts.t0 + counts.t1 + counts.t2 + counts.t3 + counts.t4 + counts.t5 + counts.t6 + counts.t7 + counts.t8

--| The number of fish after `days` days.
def fishAfter (days: Nat) (timers: List Nat): Nat :=
  Nat.iterate days Counts.nextDay (Counts.ofTimers timers) |> .total

def solvePart1 (timers: List Nat): Nat := fishAfter 80 timers

def solvePart2 (timers: List Nat): Nat := fishAfter 256 timers
