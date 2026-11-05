--| Each instruction does to the program's ship what the spec says it does
--| (`navigateFollows`, `steerFollows`), so following the whole route
--| does too, and both answers are the spec's.

namespace Aoc.Year2020.Day12.Proofs
import Aoc.Year2020.Day12 (..)
import Aoc.Year2020.Day12 (Spec)
import Aoc.Year2020.Day12.Spec (along, turned, unit)
import Std (Eq, Int, List, Nat)

--| Folding commutes with a map that commutes with each step.
theorem foldLeftRelate (relate: s → t) (f: s → a → s) (g: t → a → t) (commutes: (x: s) → (item: a) → relate (f x item) = g (relate x) item):
    (items: List a) → (x: s) → relate (items.foldLeft x f) = items.foldLeft (relate x) g
  | [], x => rfl
  | [item, ..rest], x => rewrite <- commutes x item in foldLeftRelate relate f g commutes rest (f x item)

theorem alongUnit (location: Location) (heading: Heading) (distance: Nat): along location (unit heading) distance = location.moved heading distance :=
  match heading with
    | North => Location.ext _ _ (omega) (omega)
    | South => Location.ext _ _ (omega) (omega)
    | East => Location.ext _ _ (omega) (omega)
    | West => Location.ext _ _ (omega) (omega)

--| Part 1's ship as the spec sees it: facing a step, not a heading.
def Ship.inSpec (ship: Ship): Spec.Ship := { position = ship.location, facing = unit ship.facing }

theorem navigateFollows (ship: Ship) (instruction: Instruction): Spec.navigate ship.inSpec instruction = (ship.follow instruction).inSpec :=
  match instruction with
    | { action, value } =>
      match action with
        | Move heading => rewrite alongUnit ship.location heading value in rfl
        | Turn side =>
          rewrite headingTurned (clockwiseQuarters side value) ship.facing, <- turnedClockwise side value (unit ship.facing) in rfl
        | Forward => rewrite alongUnit ship.location ship.facing value in rfl

--| Part 2's ship as the spec sees it.
def WaypointShip.inSpec (ship: WaypointShip): Spec.Steered := { position = ship.location, waypoint = ship.waypoint }

theorem steerFollows (ship: WaypointShip) (instruction: Instruction): Spec.steer ship.inSpec instruction = (ship.follow instruction).inSpec :=
  match instruction with
    | { action, value } =>
      match action with
        | Move heading => rewrite alongUnit ship.waypoint heading value in rfl
        | Turn side => rewrite rotatedTurned side value ship.waypoint in rfl
        | Forward => rfl

theorem part1Rules (route: Route): Spec.Part1 route.instructions route.shipDistance :=
  rewrite <- foldLeftRelate Ship.inSpec Ship.follow Spec.navigate (ship instruction => Eq.sym (navigateFollows ship instruction)) route.instructions Ship.start in rfl

theorem part2Rules (route: Route): Spec.Part2 route.instructions route.waypointDistance :=
  rewrite <- foldLeftRelate WaypointShip.inSpec WaypointShip.follow Spec.steer (ship instruction => Eq.sym (steerFollows ship instruction)) route.instructions WaypointShip.start in rfl
