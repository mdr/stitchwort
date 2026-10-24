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
theorem rollsCells (rows: Vec (Vec Cell w) h): countRolls rows = List.sumBy (r => List.sumBy (c => (rowsCells rows r c).count) (List.range w)) (List.range h) :=
  let gap := Vec.replicate w Floor
  calc countRolls rows
    _ = List.sumBy (r => Vec.sumBy Cell.count (Vec.getOr gap r rows)) (List.range h) := Vec.sumByGetOr (row => Vec.sumBy Cell.count row) gap rows
    _ = List.sumBy (r => List.sumBy (c => (rowsCells rows r c).count) (List.range w)) (List.range h)
      := List.sumByCong (r => Vec.sumBy Cell.count (Vec.getOr gap r rows)) (r => List.sumBy (c => (rowsCells rows r c).count) (List.range w))
        (List.range h) (r => Vec.sumByGetOr Cell.count Floor (Vec.getOr gap r rows))

-- What a round takes from one cell: 1 when it holds an accessible roll.
theorem taken: (a: Cell) -> (n: Nat) -> Cell.count a - Cell.count (keep a (n + Cell.count a)) = Bool.toNat (a == Roll && n < 4)
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
  let below := (r: Nat) => (c: Nat) => (h: grid.height <= r) => rowsCellsBelow grid.rows r c h
  let right := (r: Nat) => (c: Nat) => (h: grid.width <= c) => rowsCellsRight grid.rows r c h
  let a := (r: Nat) => (c: Nat) => (cells r c).count
  let k := (r: Nat) => (c: Nat) => (keep (cells r c) (window cells r c)).count
  let sum2 := (f: Nat -> Nat -> Nat) => List.sumBy (r => List.sumBy (c => f r c) (List.range grid.width)) (List.range grid.height)
  calc solvePart1 grid
    _ = sum2 a - sum2 (r c => (rowsCells (roundRows grid.rows) r c).count)
      := rewrite rollsCells grid.rows, rollsCells (roundRows grid.rows)
    _ = sum2 a - sum2 k
      := rewrite (List.sumByCong (r => List.sumBy (c => (rowsCells (roundRows grid.rows) r c).count) (List.range grid.width)) (r => List.sumBy (c => k r c) (List.range grid.width))
        (List.range grid.height)
        (r => List.sumByCong (c => (rowsCells (roundRows grid.rows) r c).count) (c => k r c)
          (List.range grid.width) (c => Eq.cong Cell.count (cellRound grid.rows r c))))
    _ = sum2 (r c => a r c - k r c)
      := rewrite List.sumBySub (r => List.sumBy (c => a r c) (List.range grid.width)) (r => List.sumBy (c => k r c) (List.range grid.width))
          (r => List.sumByLe (c => a r c) (c => k r c) (c => keepLe (cells r c) (window cells r c)) (List.range grid.width))
          (List.range grid.height) in
        List.sumByCong
          (r => List.sumBy (c => a r c) (List.range grid.width) - List.sumBy (c => k r c) (List.range grid.width))
          (r => List.sumBy (c => a r c - k r c) (List.range grid.width))
          (List.range grid.height)
          (r => List.sumBySub (c => a r c) (c => k r c) (c => keepLe (cells r c) (window cells r c)) (List.range grid.width))
    _ = sum2 (r c => Bool.toNat (accessible grid cells r c))
      := List.sumByCong (r => List.sumBy (c => a r c - k r c) (List.range grid.width)) (r => List.sumBy (c => Bool.toNat (accessible grid cells r c)) (List.range grid.width))
        (List.range grid.height)
        (r => List.sumByCong (c => a r c - k r c) (c => Bool.toNat (accessible grid cells r c))
          (List.range grid.width)
          (c => rewrite windowIsNeighbours grid cells below right r c in taken (cells r c) (neighbours grid cells r c)))
    _ = part1Spec grid := Eq.sym (countPositionsSum grid (r c => accessible grid cells r c))
