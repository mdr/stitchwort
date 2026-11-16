--| Each instruction does to the program's ship what the spec says it does
--| (`navigateFollows`, `steerFollows`), so following the whole route
--| does too, and both answers are the spec's.

namespace Aoc.Year2020.Day12.Proofs
import Aoc.Year2020.Day12 (..)
import Aoc.Year2020.Day12 (Spec)
import Aoc.Year2020.Day12.Spec (along, turned, unit)
import Aoc.Common (Coords, Heading)
import Std (Eq, Int, List, Nat)

--| Folding commutes with a map that commutes with each step.
theorem foldLeftRelate ∀ (relate: s → t) (f: s → a → s) (g: t → a → t)
    (commutes: ∀ (x: s) (item: a) => relate (f x item) = g (relate x) item)
    (items: List a) (x: s):
    relate (items.foldLeft x f) = items.foldLeft (relate x) g :=
  match items with
    | [] => byComputing
    | [item, ..rest] => rewrite <- commutes x item then foldLeftRelate relate f g commutes rest (f x item)

theorem alongTimes ∀ (location step: Location) (distance: Nat):
    along location step distance = location.plus (step.times distance.toInt) :=
  Coords.ext _ _ (algebra) (algebra)

theorem alongUnit ∀ (location: Location) (heading: Heading) (distance: Nat):
    along location (unit heading) distance = location.moved heading distance :=
  match heading with
    | North => Coords.ext _ _ (arithmetic) (arithmetic)
    | South => Coords.ext _ _ (arithmetic) (arithmetic)
    | East => Coords.ext _ _ (arithmetic) (arithmetic)
    | West => Coords.ext _ _ (arithmetic) (arithmetic)

--| Part 1's ship as the spec sees it: facing a step, not a heading.
def Ship.inSpec (ship: Ship): Spec.Ship := { position = ship.location, facing = unit ship.facing }

theorem navigateFollows ∀ (ship: Ship) (instruction: Instruction):
    Spec.navigate ship.inSpec instruction = (ship.follow instruction).inSpec :=
  match instruction with
    | { action, value } =>
      match action with
        | Move heading => rewrite alongUnit ship.location heading value
        | Turn side =>
          rewrite headingTurned (clockwiseQuarters side value) ship.facing, <- turnedClockwise side value
            (unit ship.facing)
        | Forward => rewrite alongUnit ship.location ship.facing value

--| Part 2's ship as the spec sees it.
def WaypointShip.inSpec (ship: WaypointShip): Spec.Steered := { position = ship.location, waypoint = ship.waypoint }

theorem steerFollows ∀ (ship: WaypointShip) (instruction: Instruction):
    Spec.steer ship.inSpec instruction = (ship.follow instruction).inSpec :=
  match instruction with
    | { action, value } =>
      match action with
        | Move heading => rewrite alongUnit ship.waypoint heading value
        | Turn side => rewrite rotatedTurned side value ship.waypoint
        | Forward => rewrite alongTimes ship.location ship.waypoint value

theorem part1Rules ∀ (route: Route): Spec.Part1 route.instructions route.shipDistance :=
  rewrite <- foldLeftRelate Ship.inSpec Ship.follow Spec.navigate
    (ship instruction => (navigateFollows ship instruction).flipped)
    route.instructions
    Ship.start

theorem part2Rules ∀ (route: Route): Spec.Part2 route.instructions route.waypointDistance :=
  rewrite <- foldLeftRelate WaypointShip.inSpec WaypointShip.follow Spec.steer
    (ship instruction => (steerFollows ship instruction).flipped)
    route.instructions
    WaypointShip.start
