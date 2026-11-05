--| Turning: the spec turns a step by quarter turns, as many as the degrees
--| say, left or right; the program reduces every turn to 0 to 3 quarter
--| turns clockwise. Four quarter turns are a full turn (`fullTurnLeft`,
--| `fullTurnRight`), so only the remainder counts, and a quarter turn left
--| is three right; so the two agree, on a heading's step
--| (`headingTurned`) and on the waypoint (`rotatedTurned`).

namespace Aoc.Year2020.Day12.Proofs
import Aoc.Year2020.Day12 (..)
import Aoc.Year2020.Day12.Spec (quarterLeft, quarterRight, turned, unit)
import Std (Eq, Int, Nat, Void)

--| Iterating a step that comes back to where it started after `period`
--| steps, a whole number of times over, comes back too.
theorem iterateCycles (f: a → a) (period: Nat) (cycle: (x: a) → Nat.iterate period f x = x): (times: Nat) → (x: a) → Nat.iterate (times * period) f x = x
  | Zero, x => rfl
  | Succ times, x => rewrite Nat.iterateAdd f period (times * period) x, cycle x in iterateCycles f period cycle times x

--| So only the remainder of the count counts.
theorem iterateMod (f: a → a) (period: Nat) [auto positive: period ≠ 0] (cycle: (x: a) → Nat.iterate period f x = x) (count: Nat) (x: a):
    Nat.iterate count f x = Nat.iterate (count % period) f x :=
  calc Nat.iterate count f x
    _ = Nat.iterate ((count / period) * period + count % period) f x := rewrite <- Nat.divModEq count period positive in rfl
    _ = Nat.iterate (count % period) f (Nat.iterate ((count / period) * period) f x) := Nat.iterateAdd f ((count / period) * period) (count % period) x
    _ = Nat.iterate (count % period) f x := rewrite iterateCycles f period cycle (count / period) x in rfl

theorem fullTurnLeft (location: Location): Nat.iterate 4 quarterLeft location = location :=
  Location.ext _ _ (omega) (omega)

theorem fullTurnRight (location: Location): Nat.iterate 4 quarterRight location = location :=
  Location.ext _ _ (omega) (omega)

--| A turn left by `quarters` is a turn right by the rest of a full turn.
theorem leftIsRight (quarters: Nat) (small: quarters < 4) (location: Location):
    Nat.iterate quarters quarterLeft location = Nat.iterate ((4 - quarters) % 4) quarterRight location :=
  match quarters with
    | 0 => rfl
    | 1 => Location.ext _ _ (omega) (omega)
    | 2 => Location.ext _ _ (omega) (omega)
    | 3 => Location.ext _ _ (omega) (omega)
    | Succ (Succ (Succ (Succ more))) => Void.exfalso (omega)

--| The spec's turn, as the program counts it: quarter turns clockwise.
theorem turnedClockwise (side: Side) (degrees: Nat) (location: Location):
    turned side degrees location = Nat.iterate (clockwiseQuarters side degrees) quarterRight location :=
  match side with
    | Right => iterateMod quarterRight 4 fullTurnRight (degrees / 90) location
    | Left =>
      rewrite iterateMod quarterLeft 4 fullTurnLeft (degrees / 90) location in
        leftIsRight (degrees / 90 % 4) (Nat.modLt (degrees / 90) 4) location

theorem unitClockwise (heading: Heading): unit heading.clockwise = quarterRight (unit heading) :=
  match heading with
    | North => rfl
    | East => rfl
    | South => rfl
    | West => rfl

--| Turning a heading is turning its step.
theorem headingTurned: (quarters: Nat) → (heading: Heading) → unit (heading.turned quarters) = Nat.iterate quarters quarterRight (unit heading)
  | Zero, heading => rfl
  | Succ quarters, heading => rewrite <- unitClockwise heading in headingTurned quarters heading.clockwise

--| The program's rotation of the waypoint is that many quarter turns right.
theorem rotatedQuarters (location: Location) (quarters: Nat) (small: quarters < 4):
    location.rotated quarters = Nat.iterate quarters quarterRight location :=
  match quarters with
    | 0 => rfl
    | 1 => rfl
    | 2 => Location.ext _ _ (omega) (omega)
    | 3 => Location.ext _ _ (omega) (omega)
    | Succ (Succ (Succ (Succ more))) => Void.exfalso (omega)

theorem quartersSmall (side: Side) (degrees: Nat): clockwiseQuarters side degrees < 4 :=
  match side with
    | Right => Nat.modLt (degrees / 90) 4
    | Left => Nat.modLt (4 - degrees / 90 % 4) 4

theorem rotatedTurned (side: Side) (degrees: Nat) (location: Location):
    location.rotated (clockwiseQuarters side degrees) = turned side degrees location :=
  rewrite turnedClockwise side degrees location in rotatedQuarters location (clockwiseQuarters side degrees) (quartersSmall side degrees)
