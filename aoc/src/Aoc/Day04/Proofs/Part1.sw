-- Day 4, part 1 proved for every grid: the printed answer is the number of
-- accessible rolls as Proofs/Spec.sw states it (`part1Correct`, at the
-- bottom). The argument: a round leaves each cell as `keep cell window`
-- (`cellRound`, Proofs/Window.sw), where the window is the 3 by 3 block
-- around it; the window is the spec's neighbours plus the cell itself
-- (`windowIsNeighbours`); and a round only removes rolls (`keepLe`), so the
-- rolls it removes add up, cell by cell, to the accessible ones (`taken`).

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Std (Bool, Eq, List, Nat, Vec)

-- The rolls of a row, and of all the rows, cell by cell.
theorem rowRolls (row: Vec Cell w): Vec.sumBy Cell.count row = List.sumBy (c => (List.getOr Floor c (Vec.toList row)).count) (List.range w) :=
  calc Vec.sumBy Cell.count row
    _ = List.sumBy Cell.count (Vec.toList row) := Vec.sumByToList Cell.count row
    _ = List.sumBy (c => (List.getOr Floor c (Vec.toList row)).count) (List.range (List.length (Vec.toList row))) := List.sumByGetOr Cell.count Floor (Vec.toList row)
    _ = List.sumBy (c => (List.getOr Floor c (Vec.toList row)).count) (List.range w) := rewrite Vec.lengthToList row

theorem rollsCells (rows: Vec (Vec Cell w) h):
    Vec.sumBy (row => Vec.sumBy Cell.count row) rows = List.sumBy (r => List.sumBy (c => (rowsCells rows r c).count) (List.range w)) (List.range h) :=
  let gap := Vec.replicate w Floor
  calc Vec.sumBy (row => Vec.sumBy Cell.count row) rows
    _ = List.sumBy (row => Vec.sumBy Cell.count row) (Vec.toList rows) := Vec.sumByToList (row => Vec.sumBy Cell.count row) rows
    _ = List.sumBy (r => Vec.sumBy Cell.count (List.getOr gap r (Vec.toList rows))) (List.range (List.length (Vec.toList rows)))
        := List.sumByGetOr (row => Vec.sumBy Cell.count row) gap (Vec.toList rows)
    _ = List.sumBy (r => Vec.sumBy Cell.count (List.getOr gap r (Vec.toList rows))) (List.range h) := rewrite Vec.lengthToList rows
    _ = List.sumBy (r => List.sumBy (c => (rowsCells rows r c).count) (List.range w)) (List.range h)
        := List.sumByCongr (r => Vec.sumBy Cell.count (List.getOr gap r (Vec.toList rows))) (r => List.sumBy (c => (rowsCells rows r c).count) (List.range w))
             (r => rowRolls (List.getOr gap r (Vec.toList rows))) (List.range h)

-- What a round takes from one cell: 1 when it holds an accessible roll.
theorem taken: (a: Cell) -> (n: Nat) -> Cell.count a - Cell.count (keep a (n + Cell.count a)) = Bool.toNat (a == Roll && n < 4)
  | Floor, n                           => rfl
  | Roll,  0                           => rfl
  | Roll,  1                           => rfl
  | Roll,  2                           => rfl
  | Roll,  3                           => rfl
  | Roll,  Succ (Succ (Succ (Succ n))) => rewrite Nat.addOne n

-- Part 1 is right for every grid: the printed answer is the number of rolls
-- with fewer than four rolls around them.
theorem part1Correct (grid: Grid): solvePart1 grid = part1Spec grid :=
  let gap := Vec.replicate grid.width Floor
  let cells := cellsOf grid
  let below := (r: Nat) => (c: Nat) => (h: grid.height <= r) => rowsCellsBelow grid.rows r c h
  let right := (r: Nat) => (c: Nat) => (h: grid.width <= c) => rowsCellsRight grid.rows r c h
  let a := (r: Nat) => (c: Nat) => (cells r c).count
  let k := (r: Nat) => (c: Nat) => (keep (cells r c) (window cells r c)).count
  let sum2 := (f: Nat -> Nat -> Nat) => List.sumBy (r => List.sumBy (c => f r c) (List.range grid.width)) (List.range grid.height)
  calc solvePart1 grid
    _ = sum2 a - sum2 (r c => (rowsCells (Vec.around gap peelRow grid.rows) r c).count)
        := rewrite rollsCells grid.rows, rollsCells (Vec.around gap peelRow grid.rows)
    _ = sum2 a - sum2 k
        := Eq.cong (t => sum2 a - t)
             (List.sumByCongr (r => List.sumBy (c => (rowsCells (Vec.around gap peelRow grid.rows) r c).count) (List.range grid.width)) (r => List.sumBy (c => k r c) (List.range grid.width))
               (r => List.sumByCongr (c => (rowsCells (Vec.around gap peelRow grid.rows) r c).count) (c => k r c)
                  (c => Eq.cong Cell.count (cellRound grid.rows r c)) (List.range grid.width))
               (List.range grid.height))
    _ = sum2 (r c => a r c - k r c)
        := rewrite List.sumBySub (r => List.sumBy (c => a r c) (List.range grid.width)) (r => List.sumBy (c => k r c) (List.range grid.width))
                 (r => List.sumByLe (c => a r c) (c => k r c) (c => keepLe (cells r c) (window cells r c)) (List.range grid.width))
                 (List.range grid.height) in
             List.sumByCongr
               (r => List.sumBy (c => a r c) (List.range grid.width) - List.sumBy (c => k r c) (List.range grid.width))
               (r => List.sumBy (c => a r c - k r c) (List.range grid.width))
               (r => List.sumBySub (c => a r c) (c => k r c) (c => keepLe (cells r c) (window cells r c)) (List.range grid.width))
               (List.range grid.height)
    _ = sum2 (r c => Bool.toNat (accessible grid cells r c))
        := List.sumByCongr (r => List.sumBy (c => a r c - k r c) (List.range grid.width)) (r => List.sumBy (c => Bool.toNat (accessible grid cells r c)) (List.range grid.width))
             (r => List.sumByCongr (c => a r c - k r c) (c => Bool.toNat (accessible grid cells r c))
                (c => rewrite windowIsNeighbours grid cells below right r c in taken (cells r c) (neighbours grid cells r c))
                (List.range grid.width))
             (List.range grid.height)
    _ = part1Spec grid := Eq.sym (countPositionsSum grid (r c => accessible grid cells r c))
