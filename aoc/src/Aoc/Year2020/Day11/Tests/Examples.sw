--| Day 11's puzzle examples: the layout, its first rounds and both answers,
--| part 2's three examples of what a passenger sees, and the program's
--| rounds against the spec's on the example.

namespace Aoc.Year2020.Day11.Tests
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11 (Spec)
import Aoc.Common (Position)
import Std (Fail, List, Nat, Option, Result, Text)

def parsed (input: Text): Result Layout Text := Fail.toResult (() => parseLayout input)

def part1 (input: Text): Result (Option Nat) Text := (parsed input).map (layout => layout.settledOccupied adjacentRule)

def part2 (input: Text): Result (Option Nat) Text :=
  (parsed input).map (layout => layout.settledOccupied layout.sightRule)

--| How many occupied seats the passenger at `at` has in view by `rule`.
def occupiedInView (layout: Layout) (rule: Rule) (at: Position): Nat :=
  let find := layout.grid.lookup
  (rule.inView find at).count (near => find near == Some Occupied)

def example: Text := """
  L.LL.LL.LL
  LLLLLLL.LL
  L.L.L..L..
  LLLL.LL.LL
  L.LL.LL.LL
  L.LLLLL.LL
  ..L.L.....
  LLLLLLLLLL
  L.LLLLLL.L
  L.LLLLL.LL
  """

--| The example after one round, by either rule: every seat fills.
def afterOne: Text := """
  #.##.##.##
  #######.##
  #.#.#..#..
  ####.##.##
  #.##.##.##
  #.#####.##
  ..#.#.....
  ##########
  #.######.#
  #.#####.##
  """

--| After two rounds of part 1's rules.
def afterTwoAdjacent: Text := """
  #.LL.L#.##
  #LLLLLL.L#
  L.L.L..L..
  #LLL.LL.L#
  #.LL.LL.LL
  #.LLLL#.##
  ..L.L.....
  #LLLLLLLL#
  #.LLLLLL.L
  #.#LLLL.##
  """

--| After two rounds of part 2's rules.
def afterTwoSight: Text := """
  #.LL.LL.L#
  #LLLLLL.LL
  L.L.L..L..
  LLLL.LL.LL
  L.LL.LL.LL
  L.LLLLL.LL
  ..L.L.....
  LLLLLLLLL#
  #.LLLLLL.L
  #.LLLLL.L#
  """

--| The empty seat at row 4, column 3 sees eight occupied seats.
def seesEight: Text := """
  .......#.
  ...#.....
  .#.......
  .........
  ..#L....#
  ....#....
  .........
  #........
  ...#.....
  """

--| The left empty seat sees only the other empty one, which hides the
--| occupied seats behind it.
def seesOne: Text := """
  .............
  .L.L.#.#.#.#.
  .............
  """

--| The empty seat in the middle sees no occupied seats.
def seesNone: Text := """
  .##.##.
  #.#.#.#
  ##...##
  ...L...
  ##...##
  #.#.#.#
  .##.##.
  """

def rounds (rule: Layout → Rule) (count: Nat) (input: Text): Result Layout Text :=
  (parsed input).map (layout => Nat.iterate count (next => next.round ((rule layout).planFor layout)) layout)

test "example, 10 rows of 10" := (parsed example).map (layout => (layout.grid.height, layout.grid.width)) == Ok (10, 10)
test "a bad character fails" := not (parsed "L.X\n").isOk
test "a ragged row fails" := not (parsed "L.L\nLL\n").isOk

test "example, part 1's first round" := rounds (_ => adjacentRule) 1 example == parsed afterOne
test "example, part 1's second round" := rounds (_ => adjacentRule) 2 example == parsed afterTwoAdjacent
test "example, part 2's first round" := rounds (.sightRule) 1 example == parsed afterOne
test "example, part 2's second round" := rounds (.sightRule) 2 example == parsed afterTwoSight

test "example, part 1" := part1 example == Ok (Some 37)
test "example, part 2" := part2 example == Ok (Some 26)

test "part 2, eight occupied in sight" :=
  (parsed seesEight).map (layout => occupiedInView layout layout.sightRule { row = 4, column = 3 }) == Ok 8
test "part 2, the near empty seat hides the rest" :=
  (parsed seesOne).map (layout =>
    (
      layout.sightRule.inView layout.grid.lookup { row = 1, column = 1 },
      occupiedInView layout layout.sightRule { row = 1, column = 1 }
    ))
    == Ok ([{ row = 1, column = 3 }], 0)
test "part 2, nothing occupied in sight" :=
  (parsed seesNone).map (layout => occupiedInView layout layout.sightRule { row = 3, column = 3 }) == Ok 0
test "part 1, the same seats see two" :=
  (parsed seesEight).map (layout => occupiedInView layout adjacentRule { row = 4, column = 3 }) == Ok 2

test "a seat alone fills and stays" := part1 "L\n" == Ok (Some 1) ∧ part2 "L\n" == Ok (Some 1)
test "floor only, nothing to fill" := part1 "...\n" == Ok (Some 0)

-- The program's rounds are the spec's, run side by side on the example.
test "spec, part 1's rounds" :=
  (parsed example).map (layout =>
    [0, 1, 2, 3, 4, 5].all (count =>
      (Nat.iterate count (next => next.round (adjacentRule.planFor layout)) layout)
        == Nat.iterate count Spec.adjacentRound layout))
    == Ok True
test "spec, part 2's rounds" :=
  (parsed example).map (layout =>
    [0, 1, 2, 3, 4, 5, 6].all (count =>
      (Nat.iterate count (next => next.round (layout.sightRule.planFor layout)) layout)
        == Nat.iterate count Spec.sightRound layout))
    == Ok True
test "spec, the example settles after 5 and 6 rounds" :=
  (parsed example).map (layout =>
    let one := Nat.iterate 5 Spec.adjacentRound layout
    let two := Nat.iterate 6 Spec.sightRound layout
    (Spec.adjacentRound one == one, Spec.occupiedSeats one, Spec.sightRound two == two, Spec.occupiedSeats two))
    == Ok (True, 37, True, 26)
test "spec, eight directions" := Spec.directions == compass
