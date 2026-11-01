-- The program's step is the spec's: its levels are `after` the spec's
-- flashers, it has as many 0s as the spec has flashes, and it is all 0s
-- exactly when every octopus flashes.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Option, Void)

-- Two sets of flashers of the same levels are the same.
theorem flashersUnique (levels: List (List Nat)) (f: (Nat, Nat) → Bool) (g: (Nat, Nat) → Bool) (ff: Flashers levels f) (fg: Flashers levels g)
    (q: (Nat, Nat)): f q = g q :=
  match e: f q with
    | True => Eq.sym (And.right ff g (And.left fg) q e)
    | False =>
      match d: g q with
        | False => rfl
        | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (And.right fg f (And.left ff) q d)))

-- The program's flashers are only on the grid.
theorem flashersOnGrid (levels: List (List Nat)): OnGrid levels (flashedAt (flashers levels)) :=
  Exists.elim (flashersStable levels) (j both => rewrite And.left both in onGridAfter levels j)

-- `mapCells` of functions equal at every cell.
theorem mapCellsCong (rows: List (List a)) (g1: (Nat, Nat) → a → b) (g2: (Nat, Nat) → a → b)
    (same: (r: Nat) → (c: Nat) → (x: a) → g1 (r, c) x = g2 (r, c) x): mapCells rows g1 = mapCells rows g2 :=
  List.mapCong (List.withIndex rows) (p => List.mapWithIndex p.snd (c cell => g1 (p.fst, c) cell))
    (p => List.mapWithIndex p.snd (c cell => g2 (p.fst, c) cell))
    (p => List.mapCong (List.withIndex p.snd) (q => g1 (p.fst, q.fst) q.snd) (q => g2 (p.fst, q.fst) q.snd) (q => same p.fst q.fst q.snd))

-- The step's levels are the spec's levels after the step, for the spec's
-- flashers (any: there is one set, `flashersUnique`).
theorem stepCorrect (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool) (spec: Flashers levels flashed): step levels = after levels flashed :=
  let program := flashersCorrect levels
  let same := flashersUnique levels (flashedAt (flashers levels)) flashed program spec
  mapCellsCong levels (at level => if flashedAt (flashers levels) at then 0 else energy (flashers levels) at level)
    (at level => if flashed at then 0 else energyIn levels flashed at level)
    (r c level =>
      let agrees := energyAgrees levels (flashers levels) (flashersOnGrid levels) r c level
      let up := energyMono levels (flashedAt (flashers levels)) flashed (q h => rewrite <- same q in h) (r, c) level
      let down := energyMono levels flashed (flashedAt (flashers levels)) (q h => rewrite same q in h) (r, c) level
      let energies: energy (flashers levels) (r, c) level = energyIn levels flashed (r, c) level := omega
      rewrite same (r, c), energies in rfl)

-- A cell is 0 after the step exactly when it flashed.
theorem zeroAfter (flashed: List (List Bool)) (at: (Nat, Nat)) (level: Nat):
    ((if flashedAt flashed at then 0 else energy flashed at level) == 0) = flashedAt flashed at :=
  match flashedAt flashed at with
    | True => rfl
    | False => rfl

-- The 0s after the step are the flashers.
theorem stepCells (levels: List (List Nat)):
    (step levels).gridCells.map (cell => cell.snd == 0) = levels.gridCells.map (cell => flashedAt (flashers levels) cell.fst) :=
  rewrite gridCellsMapCells levels (at level => if flashedAt (flashers levels) at then 0 else energy (flashers levels) at level),
    List.mapMap levels.gridCells (cell => cell.snd == 0)
      (cell => (cell.fst, if flashedAt (flashers levels) cell.fst then 0 else energy (flashers levels) cell.fst cell.snd)) in
    List.mapCong levels.gridCells _ _ (cell => zeroAfter (flashers levels) cell.fst cell.snd)

-- So the step has as many 0s as the spec has flashes...
theorem zerosCorrect (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool) (spec: Flashers levels flashed):
    zeros (step levels) = flashCount levels flashed :=
  let same := flashersUnique levels (flashedAt (flashers levels)) flashed (flashersCorrect levels) spec
  calc zeros (step levels)
    _ = ((step levels).gridCells.map (cell => cell.snd == 0)).count (b => b) := Eq.sym (List.countMap (step levels).gridCells (b => b) (cell => cell.snd == 0))
    _ = (levels.gridCells.map (cell => flashedAt (flashers levels) cell.fst)).count (b => b) := rewrite stepCells levels
    _ = levels.gridCells.count (cell => flashedAt (flashers levels) cell.fst) := List.countMap levels.gridCells (b => b) (cell => flashedAt (flashers levels) cell.fst)
    _ = flashCount levels flashed := List.countCongMem levels.gridCells _ _ (cell member => same cell.fst)

-- ...and is all 0s exactly when every octopus flashes.
theorem allZeroCorrect (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool) (spec: Flashers levels flashed):
    (step levels).gridCells.all (cell => cell.snd == 0) = levels.gridCells.all (cell => flashed cell.fst) :=
  let same := flashersUnique levels (flashedAt (flashers levels)) flashed (flashersCorrect levels) spec
  calc (step levels).gridCells.all (cell => cell.snd == 0)
    _ = ((step levels).gridCells.map (cell => cell.snd == 0)).all (b => b) := Eq.sym (List.allMapBool (step levels).gridCells (b => b) (cell => cell.snd == 0))
    _ = (levels.gridCells.map (cell => flashedAt (flashers levels) cell.fst)).all (b => b) := rewrite stepCells levels
    _ = levels.gridCells.all (cell => flashedAt (flashers levels) cell.fst) := List.allMapBool levels.gridCells (b => b) (cell => flashedAt (flashers levels) cell.fst)
    _ = levels.gridCells.all (cell => flashed cell.fst) := List.allCong levels.gridCells _ _ (cell => same cell.fst)
