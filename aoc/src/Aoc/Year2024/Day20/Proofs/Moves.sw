-- The program's moves are the puzzle's (`moveAgrees`), its graph's edges
-- are those moves, each taking one picosecond (`edgesSound`,
-- `edgesComplete`), and every move can be taken back (`moveBack`). Races
-- join (`raceAppend`).

namespace Aoc.Year2024.Day20.Proofs
import Aoc.Year2024.Day20 (..)
import Aoc.Year2024.Day20.Spec (..)
import Aoc.Year2024.Day16.Proofs (anyMember)
import Std (And, Bool, Eq, Exists, List, Nat, Option, Void)

-- The program's move is the puzzle's.
theorem moveAgrees (racetrack: Racetrack) (position: Position) (direction: Direction):
    racetrack.move position direction = moveTo racetrack position direction :=
  rfl

def opposite: Direction → Direction
  | Up => Down
  | Down => Up
  | Left => Right
  | Right => Left

-- A step back the opposite way returns to where it started.
theorem stepBack: (position: Position) → (direction: Direction) → (next: Position) → position.step direction = Some next →
    next.step (opposite direction) = Some position
  | { row, column }, Down, next, stepped => rewrite <- Option.someInjective _ _ stepped in rfl
  | { row, column }, Right, next, stepped => rewrite <- Option.someInjective _ _ stepped in rfl
  | { row, column }, Up, next, stepped =>
    match row with
      | Zero => Void.exfalso (Option.noneNotSome next stepped)
      | Succ above => rewrite <- Option.someInjective _ _ stepped in rfl
  | { row, column }, Left, next, stepped =>
    match column with
      | Zero => Void.exfalso (Option.noneNotSome next stepped)
      | Succ before => rewrite <- Option.someInjective _ _ stepped in rfl

-- A move is a step onto track.
theorem moveCases (racetrack: Racetrack) (position: Position) (direction: Direction) (next: Position)
    (moved: moveTo racetrack position direction = Some next): And (position.step direction = Some next) (onTrack racetrack next = True) :=
  match stepped: position.step direction with
    | None => Void.exfalso (Option.noneNotSome next moved)
    | Some found =>
      match onIt: onTrack racetrack found with
        | False => Void.exfalso (Option.noneNotSome next moved)
        | True => rewrite <- Option.someInjective _ _ moved in Both rfl onIt

-- A step onto track is a move.
theorem moveIntro (racetrack: Racetrack) (position: Position) (direction: Direction) (next: Position)
    (stepped: position.step direction = Some next) (onIt: onTrack racetrack next = True): moveTo racetrack position direction = Some next :=
  rewrite stepped, onIt in rfl

-- A move from track can be taken back.
theorem moveBack (racetrack: Racetrack) (position: Position) (onIt: onTrack racetrack position = True) (direction: Direction) (next: Position)
    (moved: moveTo racetrack position direction = Some next): moveTo racetrack next (opposite direction) = Some position :=
  moveIntro racetrack next (opposite direction) position (stepBack position direction next (And.left (moveCases racetrack position direction next moved)))
    onIt

theorem directionsComplete: (direction: Direction) → direction ∈ directions
  | Up => Inl rfl
  | Down => Inr (Inl rfl)
  | Left => Inr (Inr (Inl rfl))
  | Right => Inr (Inr (Inr (Inl rfl)))

-- Each edge is a move, taking one picosecond.
theorem edgesSound (racetrack: Racetrack) (position: Position) (next: Position) (weight: Nat) (edge: (next, weight) ∈ racetrack.edges position):
    And (Exists Direction (direction => moveTo racetrack position direction = Some next)) (weight = 1) :=
  let found := List.memFilterMapElim (direction => racetrack.move position direction |> .map (other => (other, 1))) (next, weight) directions edge
  Exists.elim (anyMember (direction => (racetrack.move position direction |> .map (other => (other, 1))) = Some (next, weight)) directions found)
    (direction both =>
      match moved: racetrack.move position direction with
        | None => Void.exfalso (Option.noneNotSome (next, weight) (And.right both))
        | Some other =>
          let same := Option.someInjective _ _ (And.right both)
          Both (Witness direction (Eq.trans moved (Eq.cong Some (Eq.cong Pair.fst same)))) (Eq.sym (Eq.cong Pair.snd same)))

-- Each move is an edge.
theorem edgesComplete (racetrack: Racetrack) (position: Position) (direction: Direction) (next: Position)
    (moved: moveTo racetrack position direction = Some next): (next, 1) ∈ racetrack.edges position :=
  List.memFilterMapIntro (way => racetrack.move position way |> .map (other => (other, 1))) direction (next, 1) directions
    (directionsComplete direction) (rewrite moveAgrees racetrack position direction, moved in rfl)

-- Edges lead onto track.
theorem edgeOnTrack (racetrack: Racetrack) (position: Position) (next: Position) (weight: Nat) (edge: (next, weight) ∈ racetrack.edges position):
    onTrack racetrack next = True :=
  Exists.elim (And.left (edgesSound racetrack position next weight edge)) (direction moved =>
    And.right (moveCases racetrack position direction next moved))

-- After a first move, the rest of the race.
theorem raceCons (racetrack: Racetrack) (position: Position) (direction: Direction) (next: Position)
    (moved: moveTo racetrack position direction = Some next) (rest: List Direction):
    race racetrack position (Cons direction rest) = race racetrack next rest :=
  rewrite moved in rfl

-- Moves then more moves: the more moves from where the first left off.
theorem raceAppend (racetrack: Racetrack) (more: List Direction): (position: Position) → (moves: List Direction) → (middle: Position) →
    race racetrack position moves = Some middle → race racetrack position (moves ++ more) = race racetrack middle more
  | position, Nil, middle, ended => rewrite Option.someInjective _ _ ended in rfl
  | position, Cons direction rest, middle, ended =>
    match moved: moveTo racetrack position direction with
      | None => Void.exfalso (Option.noneNotSome middle ended)
      | Some next => raceAppend racetrack more next rest middle ended

-- Moves, then one more.
theorem raceSnoc (racetrack: Racetrack) (position: Position) (moves: List Direction) (middle: Position)
    (ended: race racetrack position moves = Some middle) (direction: Direction) (next: Position)
    (moved: moveTo racetrack middle direction = Some next): race racetrack position (moves ++ [direction]) = Some next :=
  Eq.trans (raceAppend racetrack [direction] position moves middle ended) (raceCons racetrack middle direction next moved Nil)
