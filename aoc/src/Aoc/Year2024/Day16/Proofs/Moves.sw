-- The maze's graph is the puzzle's moves: each edge out of a way of
-- standing is a move and its points (`afterSound`, `afterComplete`), and
-- each edge into one is a move from an open tile (`beforeSound`,
-- `beforeComplete`). Moves keep the reindeer on open tiles.

namespace Aoc.Year2024.Day16.Proofs
import Aoc.Year2024.Day16 (..)
import Aoc.Year2024.Day16.Spec (..)
import Std (And, Bool, Eq, Exists, List, Nat, Option, Or, Void)

theorem clockwiseThenCounter: (facing: Direction) → facing.clockwise.counterclockwise = facing
  | East => rfl
  | South => rfl
  | West => rfl
  | North => rfl

theorem counterThenClockwise: (facing: Direction) → facing.counterclockwise.clockwise = facing
  | East => rfl
  | South => rfl
  | West => rfl
  | North => rfl

theorem oppositeOpposite: (facing: Direction) → facing.opposite.opposite = facing
  | East => rfl
  | South => rfl
  | West => rfl
  | North => rfl

-- A step back the opposite way returns to where it started.
theorem stepBack: (position: Position) → (facing: Direction) → (next: Position) → position.step facing = Some next →
    next.step facing.opposite = Some position
  | { row, column }, East, next, stepped => rewrite <- Option.someInjective _ _ stepped in rfl
  | { row, column }, South, next, stepped => rewrite <- Option.someInjective _ _ stepped in rfl
  | { row, column }, West, next, stepped =>
    match column with
      | Zero => Void.exfalso (Option.noneNotSome next stepped)
      | Succ before => rewrite <- Option.someInjective _ _ stepped in rfl
  | { row, column }, North, next, stepped =>
    match row with
      | Zero => Void.exfalso (Option.noneNotSome next stepped)
      | Succ above => rewrite <- Option.someInjective _ _ stepped in rfl

-- A step the opposite way is undone by a step forward.
theorem stepForwardOfBack (position: Position) (facing: Direction) (previous: Position) (stepped: position.step facing.opposite = Some previous):
    previous.step facing = Some position :=
  rewrite <- oppositeOpposite facing in stepBack position facing.opposite previous stepped

-- Moving forward onto an open tile, or not.
theorem moveForwardOpen (maze: Maze) (position: Position) (facing: Direction) (ahead: Position) (stepped: position.step facing = Some ahead)
    (open: maze.isOpen ahead = True): move maze { position, facing } Forward = Some ({ position = ahead, facing }: Reindeer) :=
  rewrite stepped, open in rfl

theorem forwardOpen (maze: Maze) (position: Position) (facing: Direction) (ahead: Position) (stepped: position.step facing = Some ahead)
    (open: maze.isOpen ahead = True): maze.forward { position, facing } = [{ position = ahead, facing }] :=
  rewrite stepped, open in rfl

theorem backwardOpen (maze: Maze) (position: Position) (facing: Direction) (behind: Position) (stepped: position.step facing.opposite = Some behind)
    (open: maze.isOpen behind = True): maze.backward { position, facing } = [{ position = behind, facing }] :=
  rewrite stepped, open in rfl

-- Each edge out of a way of standing is a move, costing its points.
theorem afterSound (maze: Maze): (reindeer: Reindeer) → (next: Reindeer) → (weight: Nat) → (next, weight) ∈ maze.after reindeer →
    Exists Move (way => And (move maze reindeer way = Some next) (way.points = weight))
  | { position, facing }, next, weight, edge =>
    match List.memAppend (next, weight) _ _ edge with
      | Inr (Inl turn) => Witness Clockwise (Both (Eq.cong Some (Eq.cong Pair.fst turn)) (Eq.cong Pair.snd turn))
      | Inr (Inr (Inl turn)) => Witness Counterclockwise (Both (Eq.cong Some (Eq.cong Pair.fst turn)) (Eq.cong Pair.snd turn))
      | Inr (Inr (Inr none)) => Void.exfalso none
      | Inl forward =>
        match stepped: position.step facing with
          | None => Void.exfalso forward
          | Some ahead =>
            match open: maze.isOpen ahead with
              | False => Void.exfalso forward
              | True =>
                match forward with
                  | Inl here =>
                    Witness Forward
                      (Both (Eq.trans (moveForwardOpen maze position facing ahead stepped open) (Eq.cong Some (Eq.cong Pair.fst here)))
                        (Eq.cong Pair.snd here))
                  | Inr none => Void.exfalso none

-- Each move is an edge out of where it starts, costing its points.
theorem afterComplete (maze: Maze): (reindeer: Reindeer) → (way: Move) → (next: Reindeer) → move maze reindeer way = Some next →
    (next, way.points) ∈ maze.after reindeer
  | { position, facing }, Clockwise, next, moved =>
    rewrite <- Option.someInjective _ _ moved in List.memAppendRight _ _ _ (Inl rfl)
  | { position, facing }, Counterclockwise, next, moved =>
    rewrite <- Option.someInjective _ _ moved in List.memAppendRight _ _ _ (Inr (Inl rfl))
  | { position, facing }, Forward, next, moved =>
    match stepped: position.step facing with
      | None => Void.exfalso (Option.noneNotSome next moved)
      | Some ahead =>
        match open: maze.isOpen ahead with
          | False => Void.exfalso (Option.noneNotSome next moved)
          | True =>
            rewrite <- Option.someInjective _ _ moved in Inl rfl

-- Each edge into a way of standing on an open tile is a move to it.
theorem beforeSound (maze: Maze): (reindeer: Reindeer) → maze.holds reindeer = True → (previous: Reindeer) → (weight: Nat) →
    (previous, weight) ∈ maze.before reindeer → Exists Move (way => And (move maze previous way = Some reindeer) (way.points = weight))
  | { position, facing }, holds, previous, weight, edge =>
    match List.memAppend (previous, weight) _ _ edge with
      | Inr (Inl turn) =>
        rewrite <- Eq.cong Pair.fst turn, <- Eq.cong Pair.snd turn in
          Witness Counterclockwise (Both (rewrite clockwiseThenCounter facing in rfl) rfl)
      | Inr (Inr (Inl turn)) =>
        rewrite <- Eq.cong Pair.fst turn, <- Eq.cong Pair.snd turn in
          Witness Clockwise (Both (rewrite counterThenClockwise facing in rfl) rfl)
      | Inr (Inr (Inr none)) => Void.exfalso none
      | Inl backward =>
        match stepped: position.step facing.opposite with
          | None => Void.exfalso backward
          | Some behind =>
            match open: maze.isOpen behind with
              | False => Void.exfalso backward
              | True =>
                match backward with
                  | Inr none => Void.exfalso none
                  | Inl here =>
                    rewrite <- Eq.cong Pair.fst here, <- Eq.cong Pair.snd here in
                      Witness Forward (Both (rewrite stepForwardOfBack position facing behind stepped, holds in rfl) rfl)

-- Each move from an open tile is an edge into where it ends.
theorem beforeComplete (maze: Maze): (reindeer: Reindeer) → maze.holds reindeer = True → (way: Move) → (next: Reindeer) →
    move maze reindeer way = Some next → (reindeer, way.points) ∈ maze.before next
  | { position, facing }, holds, Clockwise, next, moved =>
    rewrite <- Option.someInjective _ _ moved in
      List.memAppendRight _ _ _ (Inr (Inl (rewrite clockwiseThenCounter facing in rfl)))
  | { position, facing }, holds, Counterclockwise, next, moved =>
    rewrite <- Option.someInjective _ _ moved in List.memAppendRight _ _ _ (Inl (rewrite counterThenClockwise facing in rfl))
  | { position, facing }, holds, Forward, next, moved =>
    match stepped: position.step facing with
      | None => Void.exfalso (Option.noneNotSome next moved)
      | Some ahead =>
        match open: maze.isOpen ahead with
          | False => Void.exfalso (Option.noneNotSome next moved)
          | True =>
            rewrite <- Option.someInjective _ _ moved in
              let back := stepBack position facing ahead stepped
              List.memAppendLeft _ _ _ (rewrite back, holds in Inl rfl)

-- A move from an open tile ends on one.
theorem moveHolds (maze: Maze): (reindeer: Reindeer) → maze.holds reindeer = True → (way: Move) → (next: Reindeer) →
    move maze reindeer way = Some next → maze.holds next = True
  | { position, facing }, holds, Clockwise, next, moved => rewrite <- Option.someInjective _ _ moved in holds
  | { position, facing }, holds, Counterclockwise, next, moved => rewrite <- Option.someInjective _ _ moved in holds
  | { position, facing }, holds, Forward, next, moved =>
    match stepped: position.step facing with
      | None => Void.exfalso (Option.noneNotSome next moved)
      | Some ahead =>
        match open: maze.isOpen ahead with
          | False => Void.exfalso (Option.noneNotSome next moved)
          | True => rewrite <- Option.someInjective _ _ moved in open
