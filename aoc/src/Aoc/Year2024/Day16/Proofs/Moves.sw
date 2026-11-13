--| The maze's graph is the puzzle's moves: each edge out of a way of
--| standing is a move and its points (`afterSound`, `afterComplete`), and
--| each edge into one is a move from an open tile (`beforeSound`,
--| `beforeComplete`). Moves keep the reindeer on open tiles.

namespace Aoc.Year2024.Day16.Proofs
import Aoc.Year2024.Day16 (..)
import Aoc.Year2024.Day16.Spec (..)
import Aoc.Common (Direction, Heading, Position)
import Aoc.Common.Proofs (oppositeOpposite, stepOpposite)
import Std (And, Bool, Eq, Exists, List, Nat, Option, Or, Void)

--| A step the opposite way is undone by a step forward.
theorem stepForwardOfBack ∀ (position: Position) (direction: Direction) (previous: Position) (stepped: position.step direction.opposite = Some previous):
    previous.step direction = Some position :=
  rewrite <- oppositeOpposite direction in stepOpposite position direction.opposite previous stepped

--| Moving forward onto an open tile, or not.
theorem moveForwardOpen ∀ (maze: Maze) (position: Position) (facing: Heading) (ahead: Position) (stepped: position.step facing.toDirection = Some ahead)
    (open: maze.isOpen ahead = True): move maze { position, facing } Forward = Some ({ position = ahead, facing }: Reindeer) :=
  rewrite stepped, open in rfl

theorem forwardOpen ∀ (maze: Maze) (position: Position) (facing: Heading) (ahead: Position) (stepped: position.step facing.toDirection = Some ahead)
    (open: maze.isOpen ahead = True): maze.forward { position, facing } = [{ position = ahead, facing }] :=
  rewrite stepped, open in rfl

theorem backwardOpen ∀ (maze: Maze) (position: Position) (facing: Heading) (behind: Position) (stepped: position.step facing.toDirection.opposite = Some behind)
    (open: maze.isOpen behind = True): maze.backward { position, facing } = [{ position = behind, facing }] :=
  rewrite stepped, open in rfl

--| Each edge out of a way of standing is a move, costing its points.
theorem afterSound ∀ (maze: Maze) (reindeer next: Reindeer) (weight: Nat) (edge: (next, weight) ∈ maze.after reindeer):
    Exists Move (way => (move maze reindeer way = Some next) ∧ (way.points = weight)) := match reindeer with
      | { position, facing } =>
        match List.memAppend (next, weight) _ _ edge with
          | Inr (Inl turn) => Witness Clockwise (Both (Eq.cong Some (Eq.cong Pair.fst turn)) (Eq.cong Pair.snd turn))
          | Inr (Inr (Inl turn)) => Witness Counterclockwise (Both (Eq.cong Some (Eq.cong Pair.fst turn)) (Eq.cong Pair.snd turn))
          | Inr (Inr (Inr none)) => Void.exfalso none
          | Inl forward =>
            match stepped: position.step facing.toDirection with
              | Some ahead =>
                match open: maze.isOpen ahead with
                  | True =>
                    match forward with
                      | Inl here =>
                        Witness Forward
                          (Both (Eq.trans (moveForwardOpen maze position facing ahead stepped open) (Eq.cong Some (Eq.cong Pair.fst here)))
                            (Eq.cong Pair.snd here))
                      | Inr none => Void.exfalso none

--| Each move is an edge out of where it starts, costing its points.
theorem afterComplete ∀ (maze: Maze) (reindeer: Reindeer) (way: Move) (next: Reindeer) (moved: move maze reindeer way = Some next):
    (next, way.points) ∈ maze.after reindeer := match reindeer, way with
      | { position, facing }, Clockwise =>
        rewrite <- Option.someInjective moved in List.memAppendRight _ _ _ (Inl rfl)
      | { position, facing }, Counterclockwise =>
        rewrite <- Option.someInjective moved in List.memAppendRight _ _ _ (Inr (Inl rfl))
      | { position, facing }, Forward =>
        match stepped: position.step facing.toDirection with
          | Some ahead =>
            match open: maze.isOpen ahead with
              | True =>
                rewrite <- Option.someInjective moved in Inl rfl

--| Each edge into a way of standing on an open tile is a move to it.
theorem beforeSound ∀ (maze: Maze): ∀ (reindeer: Reindeer) => maze.holds reindeer = True → ∀ (previous: Reindeer) (weight: Nat) =>
    (previous, weight) ∈ maze.before reindeer → Exists Move (way => (move maze previous way = Some reindeer) ∧ (way.points = weight))
  | { position, facing }, holds, previous, weight, edge =>
    match List.memAppend (previous, weight) _ _ edge with
      | Inr (Inl turn) =>
        rewrite <- Eq.cong Pair.fst turn, <- Eq.cong Pair.snd turn in
          Witness Counterclockwise (Both (rewrite Aoc.Common.Proofs.headingTurnLeftRight facing in rfl) rfl)
      | Inr (Inr (Inl turn)) =>
        rewrite <- Eq.cong Pair.fst turn, <- Eq.cong Pair.snd turn in
          Witness Clockwise (Both (rewrite Aoc.Common.Proofs.headingTurnRightLeft facing in rfl) rfl)
      | Inr (Inr (Inr none)) => Void.exfalso none
      | Inl backward =>
        match stepped: position.step facing.toDirection.opposite with
          | Some behind =>
            match open: maze.isOpen behind with
              | True =>
                match backward with
                  | Inr none => Void.exfalso none
                  | Inl here =>
                    rewrite <- Eq.cong Pair.fst here, <- Eq.cong Pair.snd here in
                      Witness Forward (Both (rewrite stepForwardOfBack position facing.toDirection behind stepped, holds in rfl) rfl)

--| Each move from an open tile is an edge into where it ends.
theorem beforeComplete ∀ (maze: Maze): ∀ (reindeer: Reindeer) => maze.holds reindeer = True → ∀ (way: Move) (next: Reindeer) =>
    move maze reindeer way = Some next → (reindeer, way.points) ∈ maze.before next
  | { position, facing }, holds, Clockwise, next, moved =>
    rewrite <- Option.someInjective moved in
      List.memAppendRight _ _ _ (Inr (Inl (rewrite Aoc.Common.Proofs.headingTurnLeftRight facing in rfl)))
  | { position, facing }, holds, Counterclockwise, next, moved =>
    rewrite <- Option.someInjective moved in List.memAppendRight _ _ _ (Inl (rewrite Aoc.Common.Proofs.headingTurnRightLeft facing in rfl))
  | { position, facing }, holds, Forward, next, moved =>
    match stepped: position.step facing.toDirection with
      | Some ahead =>
        match open: maze.isOpen ahead with
          | True =>
            rewrite <- Option.someInjective moved in
              let back := stepOpposite position facing.toDirection ahead stepped
              List.memAppendLeft _ _ _ (rewrite back, holds in Inl rfl)

--| A move from an open tile ends on one.
theorem moveHolds ∀ (maze: Maze): ∀ (reindeer: Reindeer) => maze.holds reindeer = True → ∀ (way: Move) (next: Reindeer) =>
    move maze reindeer way = Some next → maze.holds next = True
  | { position, facing }, holds, Clockwise, next, moved => rewrite <- Option.someInjective moved in holds
  | { position, facing }, holds, Counterclockwise, next, moved => rewrite <- Option.someInjective moved in holds
  | { position, facing }, holds, Forward, next, moved =>
    match stepped: position.step facing.toDirection with
      | Some ahead =>
        match open: maze.isOpen ahead with
          | True => rewrite <- Option.someInjective moved in open
