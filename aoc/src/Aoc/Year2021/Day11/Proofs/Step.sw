--| The program's step is the spec's: its levels are `after` the spec's
--| flashers, it has as many 0s as the spec has flashes, and it is all 0s
--| exactly when every octopus flashes.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Grid, Position)
import Aoc.Common.Proofs (cellsMapCells, mapCellsCong)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Option, Void)

--| Two sets of flashers of the same cavern are the same.
theorem flashersUnique ∀ (cavern: Cavern) (f: Position → Bool) (g: Position → Bool) (ff: Flashers cavern f) (fg: Flashers cavern g)
    (q: Position): f q = g q := match e: f q with
      | True => Eq.sym (And.right ff g (And.left fg) q e)
      | False =>
        match d: g q with
          | False => rfl
          | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym e) (And.right fg f (And.left ff) q d)))

--| The program's flashers are only on the grid.
theorem flashersOnGrid ∀ (cavern: Cavern): OnGrid cavern cavern.flashers.has :=
  Exists.elim (flashersStable cavern) (j both => rewrite And.left both in onGridAfter cavern j)

--| The program's step, through the flashers' table, is the step through
--| `has` and `energy`.
theorem stepIsSpec ∀ (cavern: Cavern):
    cavern.step = cavern.map (at level => if cavern.flashers.has at then 0 else cavern.flashers.energy at level) :=
  Cavern.ext _ _ (Grid.ext _ _ (mapCellsCong cavern.grid.rows (at level => if cavern.flashers.lookup at then 0 else energyWith cavern.flashers.lookup at level)
    (at level => if cavern.flashers.has at then 0 else cavern.flashers.energy at level)
    (q level => rewrite lookupIsHas cavern.flashers q, energyWithIsEnergy cavern.flashers q level in rfl)))

--| The step's cavern is the spec's cavern after the step, for the spec's
--| flashers (any: there is one set, `flashersUnique`).
theorem stepCorrect ∀ (cavern: Cavern) (flashed: Position → Bool) (spec: Flashers cavern flashed): cavern.step = after cavern flashed :=
  rewrite stepIsSpec cavern in
    let program := flashersCorrect cavern
    let same := flashersUnique cavern cavern.flashers.has flashed program spec
    Cavern.ext _ _ (Grid.ext _ _ (mapCellsCong cavern.grid.rows (at level => if cavern.flashers.has at then 0 else cavern.flashers.energy at level)
      (at level => if flashed at then 0 else energyIn cavern flashed at level)
      (q level =>
        let agrees := energyAgrees cavern cavern.flashers (flashersOnGrid cavern) q level
        let up := energyMono cavern cavern.flashers.has flashed (p h => rewrite <- same p in h) q level
        let down := energyMono cavern flashed cavern.flashers.has (p h => rewrite same p in h) q level
        let energies: cavern.flashers.energy q level = energyIn cavern flashed q level := omega
        rewrite same q, energies in rfl)))

--| A cell is 0 after the step exactly when it flashed.
theorem zeroAfter ∀ (flashed: Flashed) (at: Position) (level: Nat):
    ((if flashed.has at then 0 else flashed.energy at level) == 0) = flashed.has at := match flashed.has at with
      | True => rfl
      | False => rfl

--| The 0s after the step are the flashers.
theorem stepCells ∀ (cavern: Cavern):
    cavern.step.cells.map (cell => cell.snd == 0) = cavern.grid.cells.map (cell => cavern.flashers.has cell.fst) :=
  rewrite stepIsSpec cavern, cellsMapCells cavern.grid.rows (at level => if cavern.flashers.has at then 0 else cavern.flashers.energy at level),
    List.mapMap cavern.grid.cells (cell => cell.snd == 0)
      (cell => (cell.fst, if cavern.flashers.has cell.fst then 0 else cavern.flashers.energy cell.fst cell.snd)) in
    List.mapCong cavern.grid.cells _ _ (cell => zeroAfter cavern.flashers cell.fst cell.snd)

--| So the step has as many 0s as the spec has flashes...
theorem zerosCorrect ∀ (cavern: Cavern) (flashed: Position → Bool) (spec: Flashers cavern flashed):
    cavern.step.zeros = flashCount cavern flashed :=
  let same := flashersUnique cavern cavern.flashers.has flashed (flashersCorrect cavern) spec
  calc cavern.step.zeros
    _ = (cavern.step.cells.map (cell => cell.snd == 0)).count (b => b) := Eq.sym (List.countMap cavern.step.cells (b => b) (cell => cell.snd == 0))
    _ = (cavern.grid.cells.map (cell => cavern.flashers.has cell.fst)).count (b => b) := rewrite stepCells cavern
    _ = cavern.grid.cells.count (cell => cavern.flashers.has cell.fst) := List.countMap cavern.grid.cells (b => b) (cell => cavern.flashers.has cell.fst)
    _ = flashCount cavern flashed := List.countCongMem _ _ _ (cell member => same cell.fst)

--| ...and is all 0s exactly when every octopus flashes.
theorem allZeroCorrect ∀ (cavern: Cavern) (flashed: Position → Bool) (spec: Flashers cavern flashed):
    cavern.step.allZero = cavern.grid.cells.all (cell => flashed cell.fst) :=
  let same := flashersUnique cavern cavern.flashers.has flashed (flashersCorrect cavern) spec
  calc cavern.step.allZero
    _ = (cavern.step.cells.map (cell => cell.snd == 0)).all (b => b) := Eq.sym (List.allMapBool cavern.step.cells (b => b) (cell => cell.snd == 0))
    _ = (cavern.grid.cells.map (cell => cavern.flashers.has cell.fst)).all (b => b) := rewrite stepCells cavern
    _ = cavern.grid.cells.all (cell => cavern.flashers.has cell.fst) := List.allMapBool cavern.grid.cells (b => b) (cell => cavern.flashers.has cell.fst)
    _ = cavern.grid.cells.all (cell => flashed cell.fst) := List.allCong cavern.grid.cells _ _ (cell => same cell.fst)
