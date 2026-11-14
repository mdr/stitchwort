--| Day 13's puzzle examples, the parser, and the sieve's steps.

namespace Aoc.Year2020.Day13.Tests
import Aoc.Year2020.Day13 (..)
import Std (Fail, List, Option, Result, Text)

def parsed (input: Text): Result Notes Text := Fail.toResult (() => parseNotes input)

def part1 (input: Text): Result (Option Nat) Text := (parsed input).map (.earliestBus)

def part2 (input: Text): Result (Option Nat) Text := (parsed input).map (.earliestLineUp)

def example: Text := """
  939
  7,13,x,x,59,x,31,19
  """

--| The puzzle's further part 2 examples give only a schedule.
def schedule (line: Text): Text := "0\n${line}"

test "the example, part 1" := part1 example == Ok (Some 295)
test "the example, part 2" := part2 example == Ok (Some 1068781)
test "17,x,13,19" := part2 (schedule "17,x,13,19") == Ok (Some 3417)
test "67,7,59,61" := part2 (schedule "67,7,59,61") == Ok (Some 754018)
test "67,x,7,59,61" := part2 (schedule "67,x,7,59,61") == Ok (Some 779210)
test "67,7,x,59,61" := part2 (schedule "67,7,x,59,61") == Ok (Some 1261476)
test "1789,37,47,1889" := part2 (schedule "1789,37,47,1889") == Ok (Some 1202161486)

test "the example's notes" :=
  parsed example
    == Ok {
      earliest = 939,
      schedule = [Listed 7, Listed 13, OutOfService, OutOfService, Listed 59, OutOfService, Listed 31, Listed 19]
    }
test "the example's buses" :=
  (parsed example).map (.buses)
    == Ok [
      { id = 7, offset = 0 },
      { id = 13, offset = 1 },
      { id = 59, offset = 4 },
      { id = 31, offset = 6 },
      { id = 19, offset = 7 }
    ]

test "bus 59 leaves at 944, 5 minutes after 939" := ({ id = 59, offset = 0 }: Bus).nextDeparture 939 == 944
test "a bus leaving as you arrive needs no wait" := part1 "10\n7,5" == Ok (Some 0)
test "on a tie the first listed bus wins" := part1 "11\n4,6" == Ok (Some 4)

test "two buses with a common factor still line up" := part2 (schedule "4,x,6") == Ok (Some 4)
test "the period after them is their lcm, 12" :=
  Alignment.start.addAll [{ id = 4, offset = 0 }, { id = 6, offset = 2 }] == Some { time = 4, period = 12 }
test "stepping by the product of the IDs would skip 16 here" := part2 (schedule "4,x,6,x,5") == Ok (Some 16)
test "buses that can never line up" := part2 (schedule "4,6") == Ok None
test "one bus lines up at once" := part2 (schedule "x,x,5") == Ok (Some 3)

test "a bus ID of 0 is rejected" := not (parsed "5\n0,7").isOk
test "an empty schedule is rejected" := not (parsed "5\n").isOk
test "a schedule with no bus in service" := part1 "5\nx,x" == Ok None
