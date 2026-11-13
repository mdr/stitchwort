--| Part 2: a walk in the program's graph is a path of the spec's, and back
--| (`walkPath`, `pathWalk`, from the shared grid code's lemmas about its
--| graphs). Std's breadth-first search finds exactly the locations some
--| walk from the low point reaches (`Graph.breadthFirstShortest`), so the
--| keys of its result are the basin, with no repeats as a map's keys have
--| none, and the map's size is the basin's (`basinSizeOpen`). A low point
--| that is a 9 has no basin, and the program says 0 (`basinSizeClosed`).

namespace Aoc.Year2021.Day09.Proofs
import Aoc.Year2021.Day09 (..)
import Aoc.Year2021.Day09.Spec (..)
import Aoc.Common (Position, adjacent, cellAt, cells, cellsEnter, cellsEnterListed)
import Aoc.Common.Proofs (canEnter, enterCost, isPathCong, isPathEnd, stepEdgeElim)
import Std (Bool, DecEq, Decidable, Eq, Exists, Graph, List, Map, Nat, Option, Void)

--| Part 2 is the product of the three largest basins' sizes, for every
--| map.
theorem part2Correct (map: HeightMap): Part2Answer map (solvePart2 map) :=
  Witness (low => map.basinSize map.graph low)
    (Both (low height member => basinSizeCorrect map low height member) (rewrite lowPointsAgree map in rfl))

--| Each low point's basin has the size the program finds.
theorem basinSizeCorrect (map: HeightMap) (low: Position) (height: Nat) (member: (low, height) ∈ lowPoints map):
    BasinSize map low (map.basinSize map.graph low) :=
  match open: map.isOpen low with
    | True => basinSizeOpen map low open
    | False => basinSizeClosed map low height member open

--| The graph can enter exactly the locations that aren't 9s.
theorem canEnterOpen (map: HeightMap) (position: Position): canEnter (cellsEnter map.grid.rows enterOpen) position = inSomeBasin map position :=
  match cellAt map.grid.rows position with
    | None => rfl
    | Some digit =>
      match digit.toNat != 9 with
        | True => rfl
        | False => rfl

--| A walk in the graph is a path, through the walk's locations...
theorem walkPath (map: HeightMap) (start: Position) (path: List (Position, Nat)) (finish: Position) (walked: map.graph.Walk start path finish):
    isPath map start (path.map Pair.fst) finish = True :=
  let entered :=
    And.left
      (Aoc.Common.Proofs.walkPath (cellsEnter map.grid.rows enterOpen) ((cells map.grid.rows).map Pair.fst)
        (position c found => cellsEnterListed map.grid.rows enterOpen position c found) start path finish walked)
  rewrite <- isPathCong (canEnter (cellsEnter map.grid.rows enterOpen)) (inSomeBasin map) (canEnterOpen map) start (path.map Pair.fst) finish in entered

--| ...and a path is a walk.
theorem pathWalk (map: HeightMap) (start: Position) (steps: List Position) (finish: Position) (path: isPath map start steps finish = True):
    map.graph.Walk start (steps.map (next => (next, enterCost (cellsEnter map.grid.rows enterOpen) next))) finish :=
  Aoc.Common.Proofs.pathWalk (cellsEnter map.grid.rows enterOpen) ((cells map.grid.rows).map Pair.fst)
    (position c found => cellsEnterListed map.grid.rows enterOpen position c found) start steps finish
    (rewrite isPathCong (canEnter (cellsEnter map.grid.rows enterOpen)) (inSomeBasin map) (canEnterOpen map) start steps finish in path)

--| A path from a location that isn't a 9 ends at one.
theorem pathOpen (map: HeightMap) (start: Position) (steps: List Position) (finish: Position) (open: inSomeBasin map start = True)
    (path: isPath map start steps finish = True): inSomeBasin map finish = True :=
  isPathEnd (inSomeBasin map) start steps finish open path

--| Every step of the graph costs 1.
theorem unitSteps (map: HeightMap) (state: Position) (next: Position) (weight: Nat) (edge: (next, weight) ∈ map.graph.edges state): weight = 1 :=
  let found := And.right (stepEdgeElim (cellsEnter map.grid.rows enterOpen) state next weight edge)
  match cellAt map.grid.rows next with
    | Some digit =>
      match digit.toNat != 9 with
        | True => Eq.sym (Option.someInjective found)

--| What the search from a low point finds is in its basin...
theorem foundInBasin (map: HeightMap) (low: Position) (open: map.isOpen low = True) (location: Position)
    (found: location ∈ (map.graph.breadthFirst [low]).keys): InBasin map low location :=
  let result := map.graph.breadthFirst [low]
  let shortest := Graph.breadthFirstShortest map.graph [low] (unitSteps map)
  Exists.elim (Map.getOfContains result location ((Map.memKeys result location).forward found)) (cost got =>
    Exists.elim (And.left shortest location cost got) (source rest =>
      Exists.elim rest (start rest2 =>
        Exists.elim rest2 (path parts =>
          let (Both isSource (Both walked _)) := parts
          match isSource with
            | Inr none => Void.exfalso none
            | Inl same =>
              let steps := walkPath map source path location walked
              let fromLow: isPath map low (path.map Pair.fst) location = True := rewrite Eq.cong Pair.fst same in steps
              Both (pathOpen map low (path.map Pair.fst) location open fromLow) (Witness (path.map Pair.fst) fromLow)))))

--| ...and the search finds everything in it.
theorem inBasinFound (map: HeightMap) (low: Position) (location: Position) (inBasin: InBasin map low location):
    location ∈ (map.graph.breadthFirst [low]).keys :=
  let result := map.graph.breadthFirst [low]
  let shortest := Graph.breadthFirstShortest map.graph [low] (unitSteps map)
  Exists.elim (And.right inBasin) (steps path =>
    let walked := pathWalk map low steps location path
    Exists.elim (And.right shortest low 0 (Inl rfl) _ location walked) (found both =>
      (Map.memKeys result location).backward (Map.containsOfGet result location found (And.left both))))

--| A low point that isn't a 9: its basin has the search's size.
theorem basinSizeOpen (map: HeightMap) (low: Position) (open: map.isOpen low = True): BasinSize map low (map.graph.breadthFirst [low]).size :=
  let result := map.graph.breadthFirst [low]
  Witness result.keys
    (Both (Map.keysDistinct result)
      (Both (location => { forward = found => foundInBasin map low open location found, backward = inBasin => inBasinFound map low location inBasin })
        (Map.lengthKeys result)))

--| A height that isn't "not 9" is 9...
theorem nineOfClosed (height: Nat) (closed: (height != 9) = False): height = 9 :=
  Decidable.elimProof (Nat.decEq height 9) (same => same) (other => Void.exfalso (Decidable.refute _ closed other))

--| ...and one that is "not 9" isn't.
theorem notNineOfOpen (height: Nat) (open: (height != 9) = True): height ≠ 9 := DecEq.neTrue open

--| A low point that is a 9 has no neighbours on the map (they would be
--| higher than 9), so no path leaves it, and it isn't in a basin itself.
theorem closedNoBasin (map: HeightMap) (low: Position) (height: Nat) (member: (low, height) ∈ lowPoints map) (closed: map.isOpen low = False)
    (location: Position) (steps: List Position) (locationOpen: inSomeBasin map location = True) (path: isPath map low steps location = True): Void :=
  match steps with
    | [] => Bool.falseNotTrue (Eq.trans (Eq.sym closed) (rewrite path.read in locationOpen))
    | [next, ..rest] =>
      let near := Bool.andLeft path
      let nextOpen := Bool.andLeft (Bool.andRight path)
      match h: map.heightAt next with
        | Some other =>
          let nextCell := memCellsOfHeight map next other h
          let lowInfo := List.memFilter map.cells _ member
          let atNext := List.allMem _ (next, other) map.cells (List.allToAll _ map.cells (And.right lowInfo)) nextCell
          let lower: (height < other) = True := rewrite near at atNext in atNext
          let below: height < other := lower
          let nine := nineOfClosed height (rewrite heightOfMemCells map low height (And.left lowInfo) at closed in closed)
          let notNine := notNineOfOpen other nextOpen
          let under10 := heightBelow10 map next other nextCell
          Void.exfalso (omega [below, nine, notNine, under10])

theorem basinSizeClosed (map: HeightMap) (low: Position) (height: Nat) (member: (low, height) ∈ lowPoints map) (closed: map.isOpen low = False):
    BasinSize map low 0 :=
  Witness []
    (Both ()
      (Both
        (location => {
          forward = none => Void.exfalso none,
          backward = inBasin =>
            Exists.elim (And.right inBasin) (steps path => closedNoBasin map low height member closed location steps (And.left inBasin) path)
        })
        rfl))
