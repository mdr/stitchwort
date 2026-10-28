-- Part 2: the search back from the end settles each way of standing for
-- the score of some moves from there to the end (`toEndCorrect`), and no
-- such moves score less (`boundToEnd`). A tile is on a best path exactly
-- when, standing there some way, the lowest scores from the start and to
-- the end add up to the lowest score (`bestTilesCorrect`).

namespace Aoc.Year2024.Day16.Proofs
import Aoc.Year2024.Day16 (..)
import Aoc.Year2024.Day16.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Graph, Iff, List, Map, Nat, Option, Or, Set, Void)

-- From `reindeer`, on an open tile, some moves end on the end tile,
-- scoring `cost`.
def ReachesEnd (maze: Maze) (reindeer: Reindeer) (cost: Nat): Prop :=
  And (maze.holds reindeer = True)
    (Exists (List Move) (moves =>
      Exists Reindeer (last => And (final maze reindeer moves = Some last) (And (last.position = maze.end) (score moves = cost)))))

-- Edges into a way of standing on an open tile come from open tiles.
theorem beforeHolds (maze: Maze): (reindeer: Reindeer) → maze.holds reindeer = True → (previous: Reindeer) → (weight: Nat) →
    (previous, weight) ∈ maze.before reindeer → maze.holds previous = True
  | { position, facing }, holds, previous, weight, edge =>
    match List.memAppend (previous, weight) _ _ edge with
      | Inr (Inl turn) => rewrite <- Eq.cong Pair.fst turn in holds
      | Inr (Inr (Inl turn)) => rewrite <- Eq.cong Pair.fst turn in holds
      | Inr (Inr (Inr none)) => Void.exfalso none
      | Inl backward =>
        match stepped: position.step facing.opposite with
          | None => Void.exfalso backward
          | Some behind =>
            match open: maze.isOpen behind with
              | False => Void.exfalso backward
              | True =>
                match backward with
                  | Inl here => rewrite <- Eq.cong Pair.fst here in open
                  | Inr none => Void.exfalso none

def endSources (maze: Maze): List (Reindeer, Nat) := maze.endReindeer.map (reindeer => (reindeer, 0))

-- A source of the search back is a way of standing on the end tile, at 0.
theorem endSource (maze: Maze) (source: Reindeer) (start: Nat) (member: (source, start) ∈ endSources maze):
    And (source.position = maze.end) (start = 0) :=
  Exists.elim (List.memMapElim (reindeer => (reindeer, 0)) (source, start) maze.endReindeer member) (reindeer both =>
    rewrite <- Eq.cong Pair.fst (And.right both), <- Eq.cong Pair.snd (And.right both) in Both (listedAtEnd maze reindeer (And.left both)) rfl)

-- The search back from the end, on a maze whose E is open.
theorem toEndCorrect (maze: Maze) (endOpen: maze.isOpen maze.end = True):
    Graph.SearchResult (maze.graph True) (endSources maze) (ReachesEnd maze) maze.toEnd :=
  Graph.distancesCorrect (maze.graph True) (endSources maze) (ReachesEnd maze)
    (source start member =>
      let (Both atEnd isZero) := endSource maze source start member
      let holds: maze.holds source = True := rewrite atEnd in endOpen
      rewrite isZero in Both holds (Witness Nil (Witness source (Both rfl (Both atEnd rfl)))))
    (state cost reaches previous weight edge =>
      let (Both holds onward) := reaches
      let before := And.right (edgeHolds maze True state previous weight edge)
      Exists.elim (beforeSound maze state holds previous weight before) (way both =>
        Exists.elim onward (moves rest =>
          Exists.elim rest (last parts =>
            let (Both ended (Both atEnd scored)) := parts
            Both (beforeHolds maze state holds previous weight before)
              (Witness (Cons way moves)
                (Witness last
                  (Both (Eq.trans (finalCons maze previous way state (And.left both) moves) ended)
                    (Both atEnd (rewrite scoreCons way moves, scored, And.right both in omega)))))))))

-- Moves from an open tile are a walk back in the maze's graph, from where
-- they end, scoring the same.
theorem movesWalkBack (maze: Maze): (reindeer: Reindeer) → maze.holds reindeer = True → (moves: List Move) → (last: Reindeer) →
    final maze reindeer moves = Some last →
    Exists (List (Reindeer, Nat)) (path => And ((maze.graph True).Walk last path reindeer) (Graph.cost path = score moves))
  | reindeer, holds, Nil, last, ended => Witness Nil (Both (Eq.sym (Option.someInjective _ _ ended)) rfl)
  | reindeer, holds, Cons way rest, last, ended =>
    match moved: move maze reindeer way with
      | None => Void.exfalso (Option.noneNotSome last ended)
      | Some next =>
        let nextHolds := moveHolds maze reindeer holds way next moved
        Exists.elim (movesWalkBack maze next nextHolds rest last ended) (path both =>
          Witness (path ++ [(reindeer, way.points)])
            (Both
              (Graph.walkSnoc (maze.graph True) last path next (And.left both) reindeer way.points
                (edgeOfMove maze True next nextHolds reindeer way.points (beforeComplete maze reindeer holds way next moved)))
              (omega [
                Graph.costAppend path [(reindeer, way.points)],
                Graph.costCons reindeer way.points Nil,
                Graph.costNil [s := Reindeer],
                scoreCons way rest,
                And.right both
              ])))

-- Moves from an open tile to the end score at least the search back's
-- bound there.
theorem boundToEnd (maze: Maze) (result: Map Reindeer Nat)
    (sourcesBound: (reindeer: Reindeer) → reindeer ∈ maze.endReindeer → Graph.Bound result 0 reindeer)
    (closed: (state: Reindeer) → (cost: Nat) → result.get state = Some cost → (previous: Reindeer) → (weight: Nat) →
      (previous, weight) ∈ (maze.graph True).edges state → Graph.Bound result (cost + weight) previous)
    (reindeer: Reindeer) (holds: maze.holds reindeer = True) (moves: List Move) (last: Reindeer) (ended: final maze reindeer moves = Some last)
    (atEnd: last.position = maze.end): Graph.Bound result (score moves) reindeer :=
  Exists.elim (movesWalkBack maze reindeer holds moves last ended) (path both =>
    let along := Graph.boundAlong (maze.graph True) result closed last 0 (sourcesBound last (endListed maze last atEnd)) path reindeer (And.left both)
    Graph.boundWeaken result (0 + Graph.cost path) (score moves) reindeer along (omega [And.right both]))

-- Moves from the start to a way of standing, then from there to the end,
-- make a path standing there.
theorem joinedPath (maze: Maze) (reindeer: Reindeer) (fromStart: Nat) (toEnd: Nat) (reached: ReachedFromStart maze reindeer fromStart)
    (reaches: ReachesEnd maze reindeer toEnd):
    Exists (List Move) (moves =>
      Exists (List Reindeer) (standings =>
        And (IsPath maze moves standings) (And (score moves = fromStart + toEnd) (reindeer ∈ standings)))) :=
  Exists.elim reached (first parts =>
    Exists.elim (And.right reaches) (second rest =>
      Exists.elim rest (last others =>
        let (Both ended (Both atEnd scored)) := others
        let whole := Eq.trans (finalAppend maze second (startingReindeer maze) first reindeer (And.left parts)) ended
        Exists.elim (finalFollow maze (startingReindeer maze) (first ++ second) last whole) (standings both =>
          Witness (first ++ second)
            (Witness standings
              (Both (Both (And.left both) (rewrite And.right both, atEnd in rfl))
                (Both (rewrite scoreAppend first second, And.right parts, scored in rfl)
                  (followVisits maze second (startingReindeer maze) first reindeer (And.left parts) standings (And.left both)))))))))

-- `contains` on a set built from a list is membership.
theorem containsFromListIff [auto ord: Ord k] (xs: List k) (key: k): Iff (Set.contains (Set.fromList xs) key = True) (key ∈ xs) := {
  forward = there =>
    List.anyTrueElim xs (x => Map.Spec.sameKey key x) (key ∈ xs) (rewrite Set.containsFromList key xs at there in there) (x member same =>
      rewrite Map.Spec.sameKeySound key x same in member),
  backward = member =>
    rewrite Set.containsFromList key xs in
      List.anyOfMem xs (x => Map.Spec.sameKey key x) key (rewrite Map.Spec.sameKeyDecide key key in DecEq.refl key) member
}

-- A tile counted for `best` is where the reindeer stands some way whose
-- scores from the start and to the end add up to `best`...
theorem tileScoring (fromStart: Map Reindeer Nat) (toEnd: Map Reindeer Nat) (best: Nat) (tile: Position)
    (there: (tilesScoring fromStart toEnd best).contains tile = True):
    Exists Reindeer (reindeer =>
      Exists Nat (first =>
        Exists Nat (second =>
          And (fromStart.get reindeer = Some first)
            (And (toEnd.get reindeer = Some second) (And (first + second = best) (reindeer.position = tile)))))) :=
  let passes := (entry: (Reindeer, Nat)) => toEnd.get entry.fst |> .map (rest => entry.snd + rest == best) |> .getOrElse False
  let listed := (containsFromListIff _ tile).forward there
  Exists.elim (List.memMapElim (entry => entry.fst.position) tile (fromStart.toList.filter passes) listed) (entry both =>
    let (Both kept passed) := List.memFilter fromStart.toList passes entry (And.left both)
    match entry with
      | (reindeer, first) =>
        let got := (Map.memToList fromStart reindeer first).forward kept
        match after: toEnd.get reindeer with
          | None => Void.exfalso (Bool.falseNotTrue passed)
          | Some second =>
            Witness reindeer (Witness first (Witness second (Both got (Both after (Both (DecEq.sound _ _ passed) (And.right both)))))))

-- ...and every such tile is counted.
theorem scoringTile (fromStart: Map Reindeer Nat) (toEnd: Map Reindeer Nat) (best: Nat) (reindeer: Reindeer) (first: Nat) (second: Nat)
    (gotFirst: fromStart.get reindeer = Some first) (gotSecond: toEnd.get reindeer = Some second) (sum: first + second = best):
    (tilesScoring fromStart toEnd best).contains reindeer.position = True :=
  let passes := (entry: (Reindeer, Nat)) => toEnd.get entry.fst |> .map (rest => entry.snd + rest == best) |> .getOrElse False
  let passed: passes (reindeer, first) = True := rewrite gotSecond, <- sum in DecEq.refl (first + second)
  let kept := List.memFilterIntro fromStart.toList passes (reindeer, first) ((Map.memToList fromStart reindeer first).backward gotFirst) passed
  (containsFromListIff _ reindeer.position).backward (List.memMap _ (reindeer, first) kept (entry => entry.fst.position))

-- On a maze whose S and E are open, with lowest score `best`, the tiles
-- the program counts are exactly those on a best path.
theorem bestTilesCorrect (maze: Maze) (startOpen: maze.isOpen maze.start = True) (endOpen: maze.isOpen maze.end = True) (best: Nat)
    (lowest: IsLowestScore maze best) (tile: Position): Iff (maze.bestTiles.contains tile = True) (OnBestPath maze best tile) :=
  let reachable: Exists (List Move) (moves => Exists (List Reindeer) (standings => IsPath maze moves standings)) :=
    Exists.elim (And.left lowest) (moves rest => Exists.elim rest (standings both => Witness moves (Witness standings (And.left both))))
  let (Both reachedAll (Both startBounds closedForward)) := fromStartCorrect maze
  let (Both reachesAll (Both endBounds closedBackward)) := toEndCorrect maze endOpen
  Exists.elim (lowestScoreCorrect maze startOpen reachable) (found both =>
    let same := lowestUnique maze found best (And.right both) lowest
    let tiles: maze.bestTiles = tilesScoring maze.fromStart maze.toEnd best := rewrite And.left both, same in rfl
    rewrite tiles in {
      forward = there =>
        Exists.elim (tileScoring maze.fromStart maze.toEnd best tile there) (reindeer rest =>
          Exists.elim rest (first rest2 =>
            Exists.elim rest2 (second parts =>
              let (Both gotFirst (Both gotSecond (Both sum at))) := parts
              Exists.elim (joinedPath maze reindeer first second (reachedAll reindeer first gotFirst) (reachesAll reindeer second gotSecond))
                (moves rest3 =>
                  Exists.elim rest3 (standings joined =>
                    let (Both path (Both scored member)) := joined
                    Witness moves
                      (Witness standings
                        (Both path
                          (Both (rewrite scored, sum in rfl)
                            (rewrite <- at in List.memMap standings reindeer member (standing => standing.position)))))))))),
      backward = onPath =>
        Exists.elim onPath (moves rest =>
          Exists.elim rest (standings parts =>
            let (Both path (Both scored member)) := parts
            Exists.elim (List.memMapElim (standing => standing.position) tile standings member) (reindeer standingThere =>
              let (Both stands at) := standingThere
              Exists.elim (followSplits maze (startingReindeer maze) moves standings (And.left path) reindeer stands) (before rest2 =>
                Exists.elim rest2 (after split =>
                  let (Both joined (Both reached remaining)) := split
                  Exists.elim (pathEnds maze moves standings path) (last ending =>
                    let (Both ended atEnd) := ending
                    let holds := finalHolds maze (startingReindeer maze) startOpen before reindeer reached
                    let fromStartBound := boundAlong maze maze.fromStart closedForward (startingReindeer maze) startOpen 0
                      (startBounds maze.startReindeer 0 (Inl rfl)) before reindeer reached
                    let toEndBound := boundToEnd maze maze.toEnd (standing listed => endBounds standing 0 (List.memMap maze.endReindeer standing listed (way => (way, 0))))
                      closedBackward reindeer holds after last (Eq.trans remaining ended) atEnd
                    Exists.elim fromStartBound (first firstBoth =>
                      Exists.elim toEndBound (second secondBoth =>
                        let parts := scoreAppend before after
                        let total: score moves = score before + score after := rewrite joined in parts
                        Exists.elim
                          (joinedPath maze reindeer first second (reachedAll reindeer first (And.left firstBoth))
                            (reachesAll reindeer second (And.left secondBoth)))
                          (otherMoves rest3 =>
                            Exists.elim rest3 (otherStandings joinedBoth =>
                              let atLeast := And.right lowest otherMoves otherStandings (And.left joinedBoth)
                              let sum: first + second = best :=
                                omega [And.right firstBoth, And.right secondBoth, total, scored, atLeast, And.left (And.right joinedBoth)]
                              rewrite <- at in
                                scoringTile maze.fromStart maze.toEnd best reindeer first second (And.left firstBoth) (And.left secondBoth) sum))))))))))
    })

-- Part 2: on a maze whose S and E are open, with lowest score `best`, the
-- answer is the number of tiles on a best path.
theorem part2Correct (maze: Maze) (startOpen: maze.isOpen maze.start = True) (endOpen: maze.isOpen maze.end = True) (best: Nat)
    (lowest: IsLowestScore maze best): CountsBestTiles maze best (solvePart2 maze) :=
  Witness maze.bestTiles (Both (tile => bestTilesCorrect maze startOpen endOpen best lowest tile) rfl)
