-- Part 1: the search from the start settles each way of standing for the
-- score of some moves there (`fromStartCorrect`), and no moves score less
-- (`boundAlong`), so the least over the end tile is the lowest score of any
-- path (`part1Correct`).

namespace Aoc.Year2024.Day16.Proofs
import Aoc.Year2024.Day16 (..)
import Aoc.Year2024.Day16.Spec (..)
import Std (And, Bool, Eq, Exists, List, Map, Nat, Option, Or, Void)

-- Some moves from the start end at `reindeer`, scoring `cost`.
def ReachedFromStart (maze: Maze) (reindeer: Reindeer) (cost: Nat): Prop :=
  Exists (List Move) (moves => And (final maze (startingReindeer maze) moves = Some reindeer) (score moves = cost))

-- A bound still holds for a larger cost.
theorem boundWeaken [auto ord: Ord s] (settled: Map s Nat) (cost: Nat) (more: Nat) (state: s) (bound: Bound settled cost state) (le: cost ≤ more):
    Bound settled more state :=
  Exists.elim bound (found both => Witness found (Both (And.left both) (omega [And.right both, le])))

-- Moves, then one more.
theorem finalSnoc (maze: Maze) (reindeer: Reindeer) (moves: List Move) (middle: Reindeer) (ended: final maze reindeer moves = Some middle)
    (way: Move) (next: Reindeer) (moved: move maze middle way = Some next): final maze reindeer (moves ++ [way]) = Some next :=
  Eq.trans (finalAppend maze [way] reindeer moves middle ended) (finalCons maze middle way next moved Nil)

theorem scoreSnoc (moves: List Move) (way: Move): score (moves ++ [way]) = score moves + way.points :=
  rewrite scoreAppend moves [way], scoreCons way Nil in omega

-- The search from the start, on a maze whose S is open.
theorem fromStartCorrect (maze: Maze) (startOpen: maze.isOpen maze.start = True):
    SearchResult (maze.graph False) [(maze.startReindeer, 0)] (ReachedFromStart maze) maze.fromStart :=
  distancesCorrect (maze.graph False) [(maze.startReindeer, 0)] (ReachedFromStart maze)
    (source start member =>
      match member with
        | Inl here => rewrite <- Eq.cong Pair.fst here, <- Eq.cong Pair.snd here in Witness Nil (Both rfl rfl)
        | Inr none => Void.exfalso none)
    (source start member =>
      match member with
        | Inl here => rewrite <- Eq.cong Pair.fst here in startOpen
        | Inr none => Void.exfalso none)
    (state cost reached next weight edge =>
      Exists.elim (afterSound maze state next weight edge) (way both =>
        Exists.elim reached (moves parts =>
          Witness (moves ++ [way])
            (Both (finalSnoc maze (startingReindeer maze) moves state (And.left parts) way next (And.left both))
              (rewrite scoreSnoc moves way, And.right parts, And.right both in rfl)))))
    (state holds next weight edge =>
      Exists.elim (afterSound maze state next weight edge) (way both => moveHolds maze state holds way next (And.left both)))

-- Along any moves, the search's bound grows by no more than their score.
theorem boundAlong (maze: Maze) (result: Map Reindeer Nat)
    (closed: (state: Reindeer) → (cost: Nat) → result.get state = Some cost → (next: Reindeer) → (weight: Nat) →
      (next, weight) ∈ maze.after state → Bound result (cost + weight) next):
    (reindeer: Reindeer) → (cost: Nat) → Bound result cost reindeer → (moves: List Move) → (last: Reindeer) →
      final maze reindeer moves = Some last → Bound result (cost + score moves) last
  | reindeer, cost, bound, Nil, last, ended =>
    rewrite <- Option.someInjective _ _ ended in boundWeaken result cost (cost + score Nil) reindeer bound (omega)
  | reindeer, cost, bound, Cons way rest, last, ended =>
    match moved: move maze reindeer way with
      | None => Void.exfalso (Option.noneNotSome last ended)
      | Some next =>
        Exists.elim bound (found both =>
          let stepped := closed reindeer found (And.left both) next way.points (afterComplete maze reindeer way next moved)
          let along := boundAlong maze result closed next (cost + way.points)
            (boundWeaken result (found + way.points) (cost + way.points) next stepped (omega [And.right both])) rest last ended
          boundWeaken result (cost + way.points + score rest) (cost + score (Cons way rest)) last along (rewrite scoreCons way rest in omega))

-- How a way of standing on the end tile is listed.
theorem endListed (maze: Maze): (reindeer: Reindeer) → reindeer.position = maze.end → reindeer ∈ maze.endReindeer
  | { position, facing }, atEnd =>
    rewrite atEnd in List.memMap directions facing (directionsComplete facing) (way => ({ position = maze.end, facing = way }: Reindeer))

-- Each listed way of standing on the end tile is on it.
theorem listedAtEnd (maze: Maze) (reindeer: Reindeer) (member: reindeer ∈ maze.endReindeer): reindeer.position = maze.end :=
  Exists.elim (memMapElim (way => ({ position = maze.end, facing = way }: Reindeer)) reindeer directions member) (facing both =>
    rewrite <- And.right both in rfl)

-- A path's moves end on the end tile.
theorem pathEnds (maze: Maze) (moves: List Move) (standings: List Reindeer) (path: IsPath maze moves standings):
    Exists Reindeer (last => And (final maze (startingReindeer maze) moves = Some last) (last.position = maze.end)) :=
  Exists.elim (followFinal maze (startingReindeer maze) moves standings (And.left path)) (last both =>
    let atEnd := And.right path
    rewrite And.right both at atEnd in Witness last (Both (And.left both) (Option.someInjective _ _ atEnd)))

-- Moves from the start ending on the end tile make a path.
theorem pathOfFinal (maze: Maze) (moves: List Move) (last: Reindeer) (ended: final maze (startingReindeer maze) moves = Some last)
    (atEnd: last.position = maze.end): Exists (List Reindeer) (standings => IsPath maze moves standings) :=
  Exists.elim (finalFollow maze (startingReindeer maze) moves last ended) (standings both =>
    Witness standings (Both (And.left both) (rewrite And.right both, atEnd in rfl)))

-- When some path reaches the end, the program's least score is the
-- lowest score of any path.
theorem lowestScoreCorrect (maze: Maze) (startOpen: maze.isOpen maze.start = True)
    (reachable: Exists (List Move) (moves => Exists (List Reindeer) (standings => IsPath maze moves standings))):
    Exists Nat (best => And (maze.lowestScore maze.fromStart = Some best) (IsLowestScore maze best)) :=
  let (Both reachedAll (Both sourcesBound closed)) := fromStartCorrect maze startOpen
  let startBound: Bound maze.fromStart 0 (startingReindeer maze) := sourcesBound maze.startReindeer 0 (Inl rfl)
  let candidates := maze.endReindeer.filterMap maze.fromStart.get
  -- Each path's score is at least some candidate.
  let pathCandidate: (moves: List Move) → (standings: List Reindeer) → IsPath maze moves standings →
      Exists Nat (found => And (found ∈ candidates) (found ≤ score moves)) :=
    moves standings path =>
      Exists.elim (pathEnds maze moves standings path) (last both =>
        Exists.elim (boundAlong maze maze.fromStart closed (startingReindeer maze) 0 startBound moves last (And.left both)) (found bound =>
          Witness found
            (Both (List.memFilterMapIntro maze.fromStart.get last found maze.endReindeer (endListed maze last (And.right both)) (And.left bound))
              (omega [And.right bound]))))
  Exists.elim reachable (moves rest =>
    Exists.elim rest (standings path =>
      Exists.elim (pathCandidate moves standings path) (found both =>
        Exists.elim (minimumSome candidates found (And.left both)) (best least =>
          Witness best
            (Both least
              (Both
                (Exists.elim (anyMember (reindeer => maze.fromStart.get reindeer = Some best) maze.endReindeer (List.memFilterMapElim maze.fromStart.get best maze.endReindeer
                    (minimumMember candidates best least))) (last parts =>
                  Exists.elim (reachedAll last best (And.right parts)) (bestMoves reached =>
                    Exists.elim (pathOfFinal maze bestMoves last (And.left reached) (listedAtEnd maze last (And.left parts))) (bestStandings isPath =>
                      Witness bestMoves (Witness bestStandings (Both isPath (And.right reached)))))))
                (otherMoves otherStandings otherPath =>
                  Exists.elim (pathCandidate otherMoves otherStandings otherPath) (other both =>
                    omega [minimumLeast candidates best least other (And.left both), And.right both]))))))))

-- Part 1: on a maze whose S is open, with some path from S to E, the
-- answer is the lowest score.
theorem part1Correct (maze: Maze) (startOpen: maze.isOpen maze.start = True)
    (reachable: Exists (List Move) (moves => Exists (List Reindeer) (standings => IsPath maze moves standings))):
    IsLowestScore maze (solvePart1 maze) :=
  Exists.elim (lowestScoreCorrect maze startOpen reachable) (best both =>
    let answer: solvePart1 maze = best := rewrite And.left both in rfl
    rewrite answer in And.right both)

-- There is only one lowest score.
theorem lowestUnique (maze: Maze) (first: Nat) (second: Nat) (isFirst: IsLowestScore maze first) (isSecond: IsLowestScore maze second):
    first = second :=
  Exists.elim (And.left isFirst) (moves rest =>
    Exists.elim rest (standings both =>
      Exists.elim (And.left isSecond) (otherMoves otherRest =>
        Exists.elim otherRest (otherStandings otherBoth =>
          omega [
            And.right isFirst otherMoves otherStandings (And.left otherBoth),
            And.right otherBoth,
            And.right isSecond moves standings (And.left both),
            And.right both
          ]))))
