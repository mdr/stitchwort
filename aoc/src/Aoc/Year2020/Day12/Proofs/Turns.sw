--| Turning: the spec turns a step by quarter turns, as many as the degrees
--| say, left or right; the program reduces every turn to 0 to 3 quarter
--| turns clockwise and turns with the library (`Coords.turned`). Four
--| quarter turns are a full turn (`fullTurnLeft`, `fullTurnRight`), so only
--| the remainder counts, and a quarter turn left is three right; so the two
--| agree, on a heading's step (`headingTurned`) and on the waypoint
--| (`rotatedTurned`).

namespace Aoc.Year2020.Day12.Proofs
import Aoc.Common (Coords, Heading, YUp)
import Aoc.Common.Proofs (coordsTurnedHeading, iterateMod)
import Aoc.Year2020.Day12 (..)
import Aoc.Year2020.Day12.Spec (quarterLeft, quarterRight, turned, unit)
import Std (Eq, Int, Nat, Void)

theorem fullTurnLeft ∀ (location: Coords YUp): Nat.iterate 4 quarterLeft location = location :=
  Coords.ext _ _ (omega) (omega)

theorem fullTurnRight ∀ (location: Coords YUp): Nat.iterate 4 quarterRight location = location :=
  Coords.ext _ _ (omega) (omega)

--| A turn left by `quarters` is a turn right by the rest of a full turn.
theorem leftIsRight ∀ (quarters: Nat)
    (small: quarters < 4) (location: Coords YUp):
    Nat.iterate quarters quarterLeft location = Nat.iterate ((4 - quarters) % 4) quarterRight location :=
  match quarters with
    | 0 => rfl
    | 1 => Coords.ext _ _ (omega) (omega)
    | 2 => Coords.ext _ _ (omega) (omega)
    | 3 => Coords.ext _ _ (omega) (omega)
    | Succ (Succ (Succ (Succ more))) => Void.exfalso (omega)

--| The spec's turn, as the program counts it: quarter turns clockwise.
theorem turnedClockwise ∀ (side: Side) (degrees: Nat) (location: Coords YUp):
    turned side degrees location = Nat.iterate (clockwiseQuarters side degrees) quarterRight location :=
  match side with
    | Right => iterateMod quarterRight 4 fullTurnRight (degrees / 90) location
    | Left =>
      rewrite iterateMod quarterLeft 4 fullTurnLeft (degrees / 90) location in
        leftIsRight (degrees / 90 % 4) (Nat.modLt (degrees / 90) 4) location

--| The program's quarter turn is the spec's.
theorem quarterRightTurn ∀ (location: Location): quarterRight location = location.turnRight :=
  Coords.ext _ _ (omega) (omega)

--| So many quarter turns right of the spec are the library's.
theorem turnedQuarters ∀ (quarters: Nat) (location: Location):
    Nat.iterate quarters quarterRight location = location.turned quarters :=
  Nat.iterateCong quarters quarterRight Coords.turnRight location quarterRightTurn

--| The spec's step is the library's step along the heading.
theorem unitStep ∀ (heading: Heading): unit heading = heading.toCoords := match heading with
  | North => Coords.ext _ _ (omega) (omega)
  | South => Coords.ext _ _ (omega) (omega)
  | East => Coords.ext _ _ (omega) (omega)
  | West => Coords.ext _ _ (omega) (omega)

--| Turning a heading is turning its step.
theorem headingTurned ∀ (quarters: Nat) (heading: Heading):
    unit (heading.turned quarters) = Nat.iterate quarters quarterRight (unit heading) :=
  rewrite unitStep (heading.turned quarters), unitStep heading, turnedQuarters quarters heading.toCoords in
    Eq.sym (coordsTurnedHeading heading quarters)

theorem rotatedTurned ∀ (side: Side) (degrees: Nat) (location: Location):
    location.turned (clockwiseQuarters side degrees) = turned side degrees location :=
  rewrite turnedClockwise side degrees location, turnedQuarters (clockwiseQuarters side degrees) location in rfl
