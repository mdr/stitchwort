-- Paths as moves: where they leave the reindeer (`final`), joining and
-- splitting them, and the ways of standing `follow` lists along them.

namespace Aoc.Year2024.Day16.Proofs
import Aoc.Year2024.Day16 (..)
import Aoc.Year2024.Day16.Spec (..)
import Std (And, Bool, Eq, Exists, List, Nat, Option, Or, Void)

-- Where the moves leave the reindeer; `None` if one runs into a wall.
def final (maze: Maze) (reindeer: Reindeer): List Move → Option Reindeer
  | Nil => Some reindeer
  | Cons first rest =>
    match move maze reindeer first with
      | Some next => final maze next rest
      | None => None

theorem scoreCons (way: Move) (rest: List Move): score (Cons way rest) = way.points + score rest := List.sumByCons rest way Move.points

theorem scoreAppend (moves: List Move) (more: List Move): score (moves ++ more) = score moves + score more :=
  List.sumByAppend moves more Move.points

-- After a first move, the rest of the path.
theorem finalCons (maze: Maze) (reindeer: Reindeer) (way: Move) (next: Reindeer) (moved: move maze reindeer way = Some next) (rest: List Move):
    final maze reindeer (Cons way rest) = final maze next rest :=
  rewrite moved in rfl

-- Moves then more moves: the more moves from where the first left off.
theorem finalAppend (maze: Maze) (more: List Move): (reindeer: Reindeer) → (moves: List Move) → (middle: Reindeer) →
    final maze reindeer moves = Some middle → final maze reindeer (moves ++ more) = final maze middle more
  | reindeer, Nil, middle, ended => rewrite Option.someInjective _ _ ended in rfl
  | reindeer, Cons way rest, middle, ended =>
    match moved: move maze reindeer way with
      | None => Void.exfalso (Option.noneNotSome middle ended)
      | Some next => finalAppend maze more next rest middle ended

-- Moves from an open tile end on one.
theorem finalHolds (maze: Maze): (reindeer: Reindeer) → maze.holds reindeer = True → (moves: List Move) → (last: Reindeer) →
    final maze reindeer moves = Some last → maze.holds last = True
  | reindeer, holds, Nil, last, ended => rewrite <- Option.someInjective _ _ ended in holds
  | reindeer, holds, Cons way rest, last, ended =>
    match moved: move maze reindeer way with
      | None => Void.exfalso (Option.noneNotSome last ended)
      | Some next => finalHolds maze next (moveHolds maze reindeer holds way next moved) rest last ended

-- The last of a list, with one more in front.
theorem lastCons: (first: a) → (rest: List a) → (last: a) → rest.last = Some last → (Cons first rest).last = Some last
  | first, Nil, last, ended => Void.exfalso (Option.noneNotSome last ended)
  | first, Cons second more, last, ended => ended

-- `follow` ends where `final` does.
theorem followFinal (maze: Maze): (reindeer: Reindeer) → (moves: List Move) → (standings: List Reindeer) →
    follow maze reindeer moves = Some standings → Exists Reindeer (last => And (final maze reindeer moves = Some last) (standings.last = Some last))
  | reindeer, Nil, standings, followed => rewrite <- Option.someInjective _ _ followed in Witness reindeer (Both rfl rfl)
  | reindeer, Cons way rest, standings, followed =>
    match moved: move maze reindeer way with
      | None => Void.exfalso (Option.noneNotSome standings followed)
      | Some next =>
        match after: follow maze next rest with
          | None => Void.exfalso (Option.noneNotSome standings followed)
          | Some later =>
            rewrite <- Option.someInjective _ _ followed in
              Exists.elim (followFinal maze next rest later after) (last both =>
                Witness last (Both (And.left both) (lastCons reindeer later last (And.right both))))

-- Moves that don't run into a wall have standings ending where they do.
theorem finalFollow (maze: Maze): (reindeer: Reindeer) → (moves: List Move) → (last: Reindeer) → final maze reindeer moves = Some last →
    Exists (List Reindeer) (standings => And (follow maze reindeer moves = Some standings) (standings.last = Some last))
  | reindeer, Nil, last, ended => rewrite <- Option.someInjective _ _ ended in Witness [reindeer] (Both rfl rfl)
  | reindeer, Cons way rest, last, ended =>
    match moved: move maze reindeer way with
      | None => Void.exfalso (Option.noneNotSome last ended)
      | Some next =>
        Exists.elim (finalFollow maze next rest last ended) (later both =>
          Witness (Cons reindeer later) (Both (rewrite And.left both in rfl) (lastCons reindeer later last (And.right both))))

-- The reindeer stands where it starts.
theorem followStarts (maze: Maze): (reindeer: Reindeer) → (moves: List Move) → (standings: List Reindeer) →
    follow maze reindeer moves = Some standings → reindeer ∈ standings
  | reindeer, Nil, standings, followed => rewrite <- Option.someInjective _ _ followed in Inl rfl
  | reindeer, Cons way rest, standings, followed =>
    match moved: move maze reindeer way with
      | None => Void.exfalso (Option.noneNotSome standings followed)
      | Some next =>
        match after: follow maze next rest with
          | None => Void.exfalso (Option.noneNotSome standings followed)
          | Some later => rewrite <- Option.someInjective _ _ followed in Inl rfl

-- The reindeer stands wherever part of the path leaves it.
theorem followVisits (maze: Maze) (more: List Move): (reindeer: Reindeer) → (moves: List Move) → (middle: Reindeer) →
    final maze reindeer moves = Some middle → (standings: List Reindeer) → follow maze reindeer (moves ++ more) = Some standings →
    middle ∈ standings
  | reindeer, Nil, middle, ended, standings, followed =>
    rewrite <- Option.someInjective _ _ ended in followStarts maze reindeer more standings followed
  | reindeer, Cons way rest, middle, ended, standings, followed =>
    match moved: move maze reindeer way with
      | None => Void.exfalso (Option.noneNotSome middle ended)
      | Some next =>
        match after: follow maze next (rest ++ more) with
          | None => Void.exfalso (Option.noneNotSome standings followed)
          | Some later =>
            rewrite <- Option.someInjective _ _ followed in Inr (followVisits maze more next rest middle ended later after)

-- A path splits where the reindeer stands along it: moves up to there, and
-- the rest from there.
theorem followSplits (maze: Maze): (reindeer: Reindeer) → (moves: List Move) → (standings: List Reindeer) →
    follow maze reindeer moves = Some standings → (middle: Reindeer) → middle ∈ standings →
    Exists (List Move) (before =>
      Exists (List Move) (after =>
        And (moves = before ++ after) (And (final maze reindeer before = Some middle) (final maze middle after = final maze reindeer moves))))
  | reindeer, Nil, standings, followed, middle, member =>
    rewrite <- Option.someInjective _ _ followed at member in
      match member with
        | Inl here => rewrite <- here in Witness Nil (Witness Nil (Both rfl (Both rfl rfl)))
        | Inr none => Void.exfalso none
  | reindeer, Cons way rest, standings, followed, middle, member =>
    match moved: move maze reindeer way with
      | None => Void.exfalso (Option.noneNotSome standings followed)
      | Some next =>
        match after: follow maze next rest with
          | None => Void.exfalso (Option.noneNotSome standings followed)
          | Some later =>
            rewrite <- Option.someInjective _ _ followed at member in
              match member with
                | Inl here => rewrite <- here in Witness Nil (Witness (Cons way rest) (Both rfl (Both rfl (finalCons maze reindeer way next moved rest))))
                | Inr inLater =>
                  Exists.elim (followSplits maze next rest later after middle inLater) (before rest2 =>
                    Exists.elim rest2 (afterwards parts =>
                      let (Both split (Both reached remaining)) := parts
                      Witness (Cons way before)
                        (Witness afterwards
                          (Both (rewrite split in rfl)
                            (Both (Eq.trans (finalCons maze reindeer way next moved before) reached)
                              remaining)))))
