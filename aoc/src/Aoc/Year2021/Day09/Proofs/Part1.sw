--| Part 1: the program checks a location's four neighbours where the spec
--| checks every location adjacent to it, and these are the same test
--| (`lowAgrees`): a neighbour off the map has no height, and every adjacent
--| location on the map is a neighbour (Facts.sw). So the program's low
--| points are the spec's, and its sum is the spec's.

namespace Aoc.Year2021.Day09.Proofs
import Aoc.Year2021.Day09 (..)
import Aoc.Year2021.Day09.Spec (..)
import Aoc.Common (Position, adjacent)
import Aoc.Common.Proofs (adjacentNeighbour, neighbourAdjacent)
import Std (Bool, Eq, List, Nat, Option, Void)

--| Part 1 is the sum of the risk levels of the low points, for every map.
theorem part1Correct ∀ (map: HeightMap): solvePart1 map = part1 map :=
  rewrite lowPointsAgree map in
    List.sumByCong (lowPoints map) (entry => entry.snd + 1) (entry => riskLevel entry.snd) (entry => Nat.addComm entry.snd 1)

--| The program's low points are the spec's.
theorem lowPointsAgree ∀ (map: HeightMap): map.lowPoints = lowPoints map :=
  List.filterCongMem map.cells (entry => map.isLowPoint entry.fst entry.snd)
    (entry => map.cells.all (other => not (adjacent entry.fst other.fst) || entry.snd < other.snd))
    (entry member => match entry with
      | (position, height) => lowAgrees map position height member)

--| At each cell, lower than its neighbours is lower than every adjacent
--| location.
theorem lowAgrees ∀ (map: HeightMap) (position: Position) (height: Nat) (member: (position, height) ∈ map.cells):
    map.isLowPoint position height = map.cells.all (other => not (adjacent position other.fst) || height < other.snd) :=
  Bool.eqOf _ _ (low => lowerThanAdjacent map position height low) (lower => lowerThanNeighbours map position height lower)

--| Lower than the neighbours: lower than every adjacent cell.
theorem lowerThanAdjacent ∀ (map: HeightMap) (position: Position) (height: Nat) (low: map.isLowPoint position height = True):
    map.cells.all (other => not (adjacent position other.fst) || height < other.snd) = True :=
  List.allOfAll _ map.cells
    (List.allOfMem _ map.cells (entry inCells =>
      match entry with
        | (other, otherHeight) =>
          match near: adjacent position other with
            | False => rfl
            | True =>
              let below := low.read other (adjacentNeighbour position other near)
              rewrite heightOfMemCells map other otherHeight inCells at below in below))

--| Lower than every adjacent cell: lower than the neighbours on the map.
theorem lowerThanNeighbours ∀ (map: HeightMap) (position: Position) (height: Nat)
    (lower: map.cells.all (other => not (adjacent position other.fst) || height < other.snd) = True): map.isLowPoint position height = True :=
  List.allOfAll _ position.neighbours
    (List.allOfMem _ position.neighbours (next isNeighbour =>
      match h: map.heightAt next with
        | None => rfl
        | Some otherHeight =>
          let atCell := lower.read (next, otherHeight) (memCellsOfHeight map next otherHeight h)
          rewrite neighbourAdjacent position next isNeighbour at atCell in atCell))
