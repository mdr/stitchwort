--| Advent of Code 2020, day 12: a ferry's navigation instructions, one a
--| line, each an action and a value: "F10", "N3", "R90". In part 1 the
--| actions move the ship north, south, east or west, turn it left or right,
--| or move it forward the way it faces; in part 2 the same letters move a
--| waypoint (north, south, east, west), turn it about the ship, or move the
--| ship to the waypoint a number of times. Each answer is the ship's
--| Manhattan distance from where it started.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day12.main < inputs/2020/day12.txt
--|
--| Every turn is a whole number of quarter turns (the parser rejects any
--| other), so a turn is worked out as 0 to 3 quarter turns clockwise. The
--| proofs, that the parser reads the puzzle's format and that both answers
--| are the puzzle's, are in `Aoc.Year2020.Day12.Proofs` (Proofs/), and the
--| tests in `Aoc.Year2020.Day12.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2020.Day12
import Aoc.Common (Coords, Heading, YUp)
import Std (Fail, IO, List, Nat, Parse)

def main(): {IO, Fail} () :=
  let route := parseRoute IO.readAll()
  IO.print "Part 1: ${route.shipDistance}"
  IO.print "Part 2: ${route.waypointDistance}"

type Side =
  | Left
  | Right

type Action =
  | Move (heading: Heading)
  | Turn (side: Side)
  | Forward

def Action.letter: Action → Text
  | Move North => "N"
  | Move South => "S"
  | Move East => "E"
  | Move West => "W"
  | Turn Left => "L"
  | Turn Right => "R"
  | Forward => "F"

def Action.isTurn: Action → Bool
  | Turn _ => True
  | _ => False

--| An action and its value: a distance, or for a turn the degrees.
type Instruction = { action: Action, value: Nat }

type Route = { instructions: List Instruction }

def actions: List Action := [Move North, Move South, Move East, Move West, Turn Left, Turn Right, Forward]

def action(): {Parse} Action := Parse.pick (actions.map (action => (action.letter, action)))

def instruction(): {Parse} Instruction :=
  let action := action()
  let value := Parse.nat()
  if action.isTurn && value % 90 != 0 then Parse.fail "a turn has to be a multiple of 90 degrees" else { action, value }

def parseRoute (input: Text): {Fail} Route := { instructions = Parse.eachLine input instruction }

--| A place relative to the ship's start, or the waypoint relative to the
--| ship: `x` so far east (west when negative) and `y` north (south when
--| negative).
type Location = Coords YUp

--| A turn of `degrees` as quarter turns clockwise, 0 to 3: a left turn
--| goes the rest of the way round to the right.
def clockwiseQuarters (side: Side) (degrees: Nat): Nat := match side with
  | Right => degrees / 90 % 4
  | Left => (4 - degrees / 90 % 4) % 4

--| Part 1's ship: where it is and which way it faces.
type Ship = { location: Location, facing: Heading }

def Ship.start: Ship := { location = Coords.zero, facing = East }

def Ship.follow (ship: Ship) (instruction: Instruction): Ship := match instruction.action with
  | Move heading => { ship | location = ship.location.moved heading instruction.value }
  | Turn side => { ship | facing = ship.facing.turned (clockwiseQuarters side instruction.value) }
  | Forward => { ship | location = ship.location.moved ship.facing instruction.value }

--| Part 2's ship: where it is, and where the waypoint is from it.
type WaypointShip = { location: Location, waypoint: Location }

def WaypointShip.start: WaypointShip := { location = Coords.zero, waypoint = { x = 10, y = 1 } }

def WaypointShip.follow (ship: WaypointShip) (instruction: Instruction): WaypointShip := match instruction.action with
  | Move heading => { ship | waypoint = ship.waypoint.moved heading instruction.value }
  | Turn side => { ship | waypoint = ship.waypoint.turned (clockwiseQuarters side instruction.value) }
  | Forward => { ship | location = ship.location.plus (ship.waypoint.times instruction.value.toInt) }

--| Part 1: how far the ship ends from its start.
def Route.shipDistance (route: Route): Nat := (route.instructions.foldLeft Ship.start Ship.follow).location.manhattan

--| Part 2: how far the ship ends from its start, steered by the waypoint.
def Route.waypointDistance (route: Route): Nat := (route.instructions.foldLeft WaypointShip.start WaypointShip.follow).location.manhattan
