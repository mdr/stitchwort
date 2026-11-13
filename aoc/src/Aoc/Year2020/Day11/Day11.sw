--| Advent of Code 2020, day 11: a waiting area's seat layout, a grid of
--| floor (`.`), empty seats (`L`) and occupied ones (`#`). In each round
--| every seat changes at once: an empty seat with no occupied seat in view
--| fills, and an occupied one with too many occupied seats in view empties.
--| The rounds go on until one changes nothing; the answer is the number of
--| occupied seats then. In part 1 a passenger looks at the eight seats
--| around, and four occupied ones are too many; in part 2 at the first seat
--| in each of the eight directions, past any floor, and five are too many.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day11.main < inputs/2020/day11.txt
--|
--| Nothing in the rules bounds the number of rounds, so the rounds stop
--| after `roundLimit`, which is far more than any input needs. Floor never
--| changes, so the seats each passenger looks at are worked out once
--| (`Rule.planFor`), and each round looks up only those. The proofs,
--| that a round is the puzzle's round and that both answers are the
--| occupied seats of the layout the rounds settle on, are in
--| `Aoc.Year2020.Day11.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2020.Day11.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2020.Day11
import Aoc.Common (Grid, Offset, Position, parseGrid)
import Std (Fail, IO, Int, List, Map, Option, Parse)

def main(): {IO, Fail} () :=
  let layout := parseLayout IO.readAll()
  IO.print "Part 1: ${layout.settledOccupied adjacentRule |> .orFail "the seats didn't settle within ${roundLimit} rounds"}"
  IO.print "Part 2: ${layout.settledOccupied layout.sightRule |> .orFail "the seats didn't settle within ${roundLimit} rounds"}"

type Seat =
  | Floor
  | Empty
  | Occupied

--| How the layout writes a seat.
def Seat.symbol: Seat → Text
  | Floor => "."
  | Empty => "L"
  | Occupied => "#"

def seat(): {Parse} Seat := Parse.pick ([Floor, Empty, Occupied].map (seat => (seat.symbol, seat)))

type Layout = { grid: Grid Seat }

--| One row of the layout per line, every row as long as the first.
def parseLayout (input: Text): {Fail} Layout := { grid = parseGrid input seat }

def Layout.occupied (layout: Layout): Nat := layout.grid.cells.count (((_, here)) => here == Occupied)

--| How a passenger decides: the seats they look at from `at` (given what
--| is at each position, `None` off the layout), and how many of those
--| occupied make them leave.
type Rule = { inView: (Position → Option Seat) → Position → List Position, tolerance: Nat }

--| The eight directions, as one step each: up, down, across and diagonal.
def compass: List Offset := [
  { rows = -1, columns = -1 },
  { rows = -1, columns = 0 },
  { rows = -1, columns = 1 },
  { rows = 0, columns = -1 },
  { rows = 0, columns = 1 },
  { rows = 1, columns = -1 },
  { rows = 1, columns = 0 },
  { rows = 1, columns = 1 }
]

--| Part 1: the eight positions around, and four occupied are too many.
def adjacentRule: Rule := { inView = _ at => at.around, tolerance = 4 }

--| The first seat from `from` in `direction`, `distance` steps away or
--| further, past any floor; none if the edge comes first, or after
--| `steps` more steps.
def firstSeat (find: Position → Option Seat) (from: Position) (direction: Offset) (distance: Nat): (steps: Nat) → Option Position
  | Zero => None
  | Succ more =>
    match from.offset (direction.times distance.toInt) with
      | None => None
      | Some next =>
        match find next with
          | None => None
          | Some Floor => firstSeat find from direction (distance + 1) more
          | Some _ => Some next

--| Part 2: the first seat in each of the eight directions, and five
--| occupied are too many. A line of sight leaves the layout within its
--| height plus its width steps.
def Layout.sightRule (layout: Layout): Rule :=
  let reach := layout.grid.height + layout.grid.width
  { inView = find at => compass.filterMap (direction => firstSeat find at direction (distance := 1) (steps := reach)), tolerance = 5 }

--| The seat after a round, with `occupiedInView` of the seats it looks at
--| occupied.
def Seat.next (seat: Seat) (occupiedInView: Nat) (tolerance: Nat): Seat := match seat with
  | Floor => Floor
  | Empty => if occupiedInView == 0 then Occupied else Empty
  | Occupied => if tolerance <= occupiedInView then Empty else Occupied

def Seat.isSeat (seat: Seat): Bool := seat != Floor

--| A rule worked out for one floor plan: the seats a passenger at each
--| position looks at, and how many of them occupied are too many.
type Plan = { inView: Position → List Position, tolerance: Nat }

--| `rule` for the floor plan of `layout`, worked out once: floor never
--| changes, so neither do the seats in view. Only seats look, and only at
--| seats; off the layout, nothing.
def Rule.planFor (rule: Rule) (layout: Layout): Plan :=
  let find := layout.grid.lookup
  let looks := (at: Position) (here: Seat) => if here.isSeat then rule.inView find at |> .filter (near => (find near).any (.isSeat)) else []
  { inView = layout.grid.map looks |> .lookupOr [], tolerance = rule.tolerance }

--| Every seat changes at once, by what was in view before the round.
def Layout.round (layout: Layout) (plan: Plan): Layout :=
  let find := layout.grid.lookup
  { grid = layout.grid.map (at here => here.next ((plan.inView at).count (near => find near == Some Occupied)) plan.tolerance) }

--| How many rounds to run before giving up.
def roundLimit: Nat := 1000

--| Rounds from `layout` until one changes nothing, giving the layout
--| then; none after `rounds` rounds.
def Layout.settle (layout: Layout) (plan: Plan): (rounds: Nat) → Option Layout
  | Zero => None
  | Succ more =>
    let next := layout.round plan
    if next == layout then Some layout else next.settle plan more

--| The occupied seats once the rounds settle.
def Layout.settledOccupied (layout: Layout) (rule: Rule): Option Nat := layout.settle (rule.planFor layout) roundLimit |> .map (.occupied)
