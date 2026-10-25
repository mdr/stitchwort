-- Day 4, part 1 proved for every grid: the printed answer is the number of
-- accessible rolls as Spec/Spec.sw states it (`part1Correct`, at the
-- bottom). The argument: a round leaves each cell as `keep cell window`
-- (`cellRound`, Proofs/Window.sw), where the window is the 3 by 3 block
-- around it; the window is the spec's neighbours plus the cell itself
-- (`windowIsNeighbours`); and a round only removes rolls (`keepLe`), so the
-- rolls it removes add up, cell by cell, to the accessible ones (`taken`).

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Aoc.Day04.Spec (..)
import Std (Bool, Eq, List, Nat, Vec)

-- The rolls of all the rows, cell by cell.
theorem rollsCells (rows: Vec (Vec Cell w) h): countRolls rows = List.sumBy (List.range h) (r => List.sumBy (List.range w) (c => (rowsCells rows r c).count)) :=
  let gap := Vec.replicate w Floor
  calc countRolls rows
    _ = List.sumBy (List.range h) (r => Vec.sumBy (Vec.getOr rows gap r) Cell.count) := Vec.sumByGetOr rows gap (row => Vec.sumBy row Cell.count)
    _ = List.sumBy (List.range h) (r => List.sumBy (List.range w) (c => (rowsCells rows r c).count))
      := rewrite Vec.sumByGetOr _ Floor Cell.count

-- What a round takes from one cell: 1 when it holds an accessible roll.
theorem taken: (a: Cell) → (n: Nat) → Cell.count a - Cell.count (keep a (n + Cell.count a)) = Bool.toNat (a == Roll ∧ n < 4)
  | Floor, n => rfl
  | Roll, n =>
    rewrite keepRemove Roll n in
      match Nat.leq (Succ n) 4 with
        | True => rfl
        | False => rfl

-- Part 1 is right for every grid: the printed answer is the number of rolls
-- with fewer than four rolls around them.
theorem part1Correct (grid: Grid): solvePart1 grid = part1Spec grid :=
  let cells := cellsOf grid
  let below := (r: Nat) => (c: Nat) => (h: grid.height ≤ r) => rowsCellsBelow grid.rows r c h
  let right := (r: Nat) => (c: Nat) => (h: grid.width ≤ c) => rowsCellsRight grid.rows r c h
  let a := (r: Nat) => (c: Nat) => (cells r c).count
  let k := (r: Nat) => (c: Nat) => (keep (cells r c) (window cells r c)).count
  let sum2 := (f: Nat → Nat → Nat) => List.sumBy (List.range grid.height) (r => List.sumBy (List.range grid.width) (c => f r c))
  calc solvePart1 grid
    _ = sum2 a - sum2 (r c => (rowsCells (roundRows grid.rows) r c).count)
      := rewrite rollsCells grid.rows, rollsCells (roundRows grid.rows)
    _ = sum2 a - sum2 k
      := rewrite cellRound grid.rows _ _
    _ = sum2 (r c => a r c - k r c)
      := rewrite List.sumBySub (List.range grid.height) (r => List.sumBy (List.range grid.width) (c => a r c))
        (r => List.sumBy (List.range grid.width) (c => k r c))
        (r => List.sumByLe (List.range grid.width) (c => a r c) (c => k r c) (c => keepLe (cells r c) (window cells r c))),
        List.sumBySub _ (c => a _ c) (c => k _ c) (c => keepLe (cells _ c) (window cells _ c))
    _ = sum2 (r c => Bool.toNat (accessible grid cells r c))
      := rewrite windowIsNeighbours grid cells below right _ _, taken _ _
    _ = part1Spec grid := Eq.sym (countPositionsSum grid (r c => accessible grid cells r c))
