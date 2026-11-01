-- The program's step is the spec's: its levels are `after` the spec's
-- flashers, it has as many 0s as the spec has flashes, and it is all 0s
-- exactly when every octopus flashes.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Position, cellAt, cells, mapCells)
import Aoc.Common.Proofs (cellsMapCells, mapCellsCong)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Option, Void)

-- Two sets of flashers of the same levels are the same.
theorem flashersUnique (levels: List (List Nat)) (f: Position → Bool) (g: Position → Bool) (ff: Flashers levels f) (fg: Flashers levels g)
    (q: Position): f q = g q :=
  match e: f q with
    | True => Eq.sym (And.right ff g (And.left fg) q e)
    | False =>
      match d: g q with
        | False => rfl
        | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (And.right fg f (And.left ff) q d)))

-- The program's flashers are only on the grid.
theorem flashersOnGrid (levels: List (List Nat)): OnGrid levels (flashedAt (flashers levels)) :=
  Exists.elim (flashersStable levels) (j both => rewrite And.left both in onGridAfter levels j)

-- The step's levels are the spec's levels after the step, for the spec's
-- flashers (any: there is one set, `flashersUnique`).
theorem stepCorrect (levels: List (List Nat)) (flashed: Position → Bool) (spec: Flashers levels flashed): step levels = after levels flashed :=
  let program := flashersCorrect levels
  let same := flashersUnique levels (flashedAt (flashers levels)) flashed program spec
  mapCellsCong levels (at level => if flashedAt (flashers levels) at then 0 else energy (flashers levels) at level)
    (at level => if flashed at then 0 else energyIn levels flashed at level)
    (q level =>
      let agrees := energyAgrees levels (flashers levels) (flashersOnGrid levels) q level
      let up := energyMono levels (flashedAt (flashers levels)) flashed (p h => rewrite <- same p in h) q level
      let down := energyMono levels flashed (flashedAt (flashers levels)) (p h => rewrite same p in h) q level
      let energies: energy (flashers levels) q level = energyIn levels flashed q level := omega
      rewrite same q, energies in rfl)

-- A cell is 0 after the step exactly when it flashed.
theorem zeroAfter (flashed: List (List Bool)) (at: Position) (level: Nat):
    ((if flashedAt flashed at then 0 else energy flashed at level) == 0) = flashedAt flashed at :=
  match flashedAt flashed at with
    | True => rfl
    | False => rfl

-- The 0s after the step are the flashers.
theorem stepCells (levels: List (List Nat)):
    (cells (step levels)).map (cell => cell.snd == 0) = (cells levels).map (cell => flashedAt (flashers levels) cell.fst) :=
  rewrite cellsMapCells levels (at level => if flashedAt (flashers levels) at then 0 else energy (flashers levels) at level),
    List.mapMap (cells levels) (cell => cell.snd == 0)
      (cell => (cell.fst, if flashedAt (flashers levels) cell.fst then 0 else energy (flashers levels) cell.fst cell.snd)) in
    List.mapCong (cells levels) _ _ (cell => zeroAfter (flashers levels) cell.fst cell.snd)

-- So the step has as many 0s as the spec has flashes...
theorem zerosCorrect (levels: List (List Nat)) (flashed: Position → Bool) (spec: Flashers levels flashed):
    zeros (step levels) = flashCount levels flashed :=
  let same := flashersUnique levels (flashedAt (flashers levels)) flashed (flashersCorrect levels) spec
  calc zeros (step levels)
    _ = ((cells (step levels)).map (cell => cell.snd == 0)).count (b => b) := Eq.sym (List.countMap (cells (step levels)) (b => b) (cell => cell.snd == 0))
    _ = ((cells levels).map (cell => flashedAt (flashers levels) cell.fst)).count (b => b) := rewrite stepCells levels
    _ = (cells levels).count (cell => flashedAt (flashers levels) cell.fst) := List.countMap (cells levels) (b => b) (cell => flashedAt (flashers levels) cell.fst)
    _ = flashCount levels flashed := List.countCongMem (cells levels) _ _ (cell member => same cell.fst)

-- ...and is all 0s exactly when every octopus flashes.
theorem allZeroCorrect (levels: List (List Nat)) (flashed: Position → Bool) (spec: Flashers levels flashed):
    (cells (step levels)).all (cell => cell.snd == 0) = (cells levels).all (cell => flashed cell.fst) :=
  let same := flashersUnique levels (flashedAt (flashers levels)) flashed (flashersCorrect levels) spec
  calc (cells (step levels)).all (cell => cell.snd == 0)
    _ = ((cells (step levels)).map (cell => cell.snd == 0)).all (b => b) := Eq.sym (List.allMapBool (cells (step levels)) (b => b) (cell => cell.snd == 0))
    _ = ((cells levels).map (cell => flashedAt (flashers levels) cell.fst)).all (b => b) := rewrite stepCells levels
    _ = (cells levels).all (cell => flashedAt (flashers levels) cell.fst) := List.allMapBool (cells levels) (b => b) (cell => flashedAt (flashers levels) cell.fst)
    _ = (cells levels).all (cell => flashed cell.fst) := List.allCong (cells levels) _ _ (cell => same cell.fst)
