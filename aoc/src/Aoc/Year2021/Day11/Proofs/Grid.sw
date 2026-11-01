-- Grids as lists of rows: the cell at a position after `mapCells`, the
-- cells (std's `gridCells`) after `mapCells`, a cell of `gridCells` as the
-- cell at its position, and that no position is in `gridCells` twice.
-- Nothing here is about octopuses.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Std (Eq, Exists, Iff, List, Nat, Option, Void)

-- The cell at (r, c) after `mapCells` is `f` of the cell there before.
theorem cellAtMapCells (rows: List (List a)) (f: (Nat, Nat) → a → b) (r: Nat) (c: Nat):
    cellAt (mapCells rows f) (r, c) = Option.map (cellAt rows (r, c)) (f (r, c)) :=
  rewrite List.getMapWithIndex rows (r row => row.mapWithIndex (c cell => f (r, c) cell)) r in
  match List.get rows r with
    | None => rfl
    | Some row => List.getMapWithIndex row (c cell => f (r, c) cell) c

-- `gridCells` has `x` at (r, c) exactly when the cell there is `x`.
theorem memGridCellsAt (rows: List (List a)) (r: Nat) (c: Nat) (x: a): Iff (((r, c), x) ∈ rows.gridCells) (cellAt rows (r, c) = Some x) := {
  forward = member =>
    Exists.elim ((List.memGridCells rows r c x).forward member) (cells both =>
      let (Both atRow atColumn) := both
      rewrite atRow in atColumn),
  backward = found =>
    (List.memGridCells rows r c x).backward (cellAtElim rows r c x found)
}

-- The cell at (r, c), taken apart: row r, and its element c.
theorem cellAtElim (rows: List (List a)) (r: Nat) (c: Nat) (x: a) (found: cellAt rows (r, c) = Some x):
    ∃ (cells: List a) => List.get rows r = Some cells ∧ List.get cells c = Some x :=
  match e: List.get rows r with
    | None => Void.exfalso (Option.noneNotSome x found)
    | Some row => Witness row (Both rfl found)

-- The cells after `mapCells` are the cells before, each `f`'d.
theorem gridCellsMapCells (rows: List (List a)) (f: (Nat, Nat) → a → b):
    (mapCells rows f).gridCells = rows.gridCells.map (((at, x)) => (at, f at x)) :=
  calc (mapCells rows f).gridCells
    _ = List.concat (List.map (List.withIndex rows) (p => rowCells p.fst (List.mapWithIndex p.snd (c cell => f (p.fst, c) cell))))
      := rewrite withIndexFromMap 0 rows (p => List.mapWithIndex p.snd (c cell => f (p.fst, c) cell)),
        List.mapMap (List.withIndex rows) (q => rowCells q.fst q.snd) (p => (p.fst, List.mapWithIndex p.snd (c cell => f (p.fst, c) cell)))
    _ = List.concat (List.map (List.withIndex rows) (p => List.map (rowCells p.fst p.snd) (((at, x)) => (at, f at x))))
      := Eq.cong List.concat (List.mapCong (List.withIndex rows) _ _ (p => rowCellsMapWithIndex p.fst p.snd f))
    _ = rows.gridCells.map (((at, x)) => (at, f at x))
      := Eq.sym (rewrite mapConcat (List.map (List.withIndex rows) (p => rowCells p.fst p.snd)) (((at, x)) => (at, f at x)),
        List.mapMap (List.withIndex rows) (xs => List.map xs (((at, x)) => (at, f at x))) (p => rowCells p.fst p.snd) in rfl)

-- Row r's cells, as `gridCells` makes them.
def rowCells (r: Nat) (row: List a): List ((Nat, Nat), a) := row.withIndex |> .map (((c, cell)) => ((r, c), cell))

-- Row r's cells after `mapCells`.
theorem rowCellsMapWithIndex (r: Nat) (row: List a) (f: (Nat, Nat) → a → b):
    rowCells r (List.mapWithIndex row (c cell => f (r, c) cell)) = List.map (rowCells r row) (((at, x)) => (at, f at x)) :=
  rewrite withIndexFromMap 0 row (q => f (r, q.fst) q.snd),
    List.mapMap (List.withIndex row) (((c, cell)) => ((r, c), cell)) (q => (q.fst, f (r, q.fst) q.snd)),
    List.mapMap (List.withIndex row) (((at, x)) => (at, f at x)) (((c, cell)) => ((r, c), cell)) in rfl

-- `withIndexFrom s` of a list made by mapping over `withIndexFrom s`: the
-- indices are the same.
theorem withIndexFromMap: (s: Nat) → (xs: List a) → (h: (Nat, a) → b) →
    List.withIndexFrom s (List.map (List.withIndexFrom s xs) h) = List.map (List.withIndexFrom s xs) (p => (p.fst, h p))
  | s, Nil, h => rfl
  | s, Cons x rest, h => Eq.cong (Cons (s, h (s, x))) (withIndexFromMap (Succ s) rest h)

-- `map` of a `concat` is the `concat` of the `map`s.
theorem mapConcat: (xss: List (List a)) → (k: a → b) → List.map (List.concat xss) k = List.concat (List.map xss (xs => List.map xs k))
  | Nil, k => rfl
  | Cons xs rest, k => rewrite List.mapAppend xs (List.concat rest) k, mapConcat rest k in rfl

-- No position is in `gridCells` twice.
theorem positionsDistinct (rows: List (List a)): List.Distinct (rows.gridCells.map Pair.fst) := rowsDistinct 0 rows

-- The positions of the cells of rows s, s + 1, …: no repeats.
theorem rowsDistinct: (s: Nat) → (rows: List (List a)) →
    List.Distinct (List.map (List.concat (List.map (List.withIndexFrom s rows) (p => rowCells p.fst p.snd))) Pair.fst)
  | s, Nil => Trivial
  | s, Cons row rest =>
    let later := List.concat (List.map (List.withIndexFrom (Succ s) rest) (p => rowCells p.fst p.snd))
    rewrite List.mapAppend (rowCells s row) later Pair.fst in
      List.distinctAppend (List.map (rowCells s row) Pair.fst) (List.map later Pair.fst)
        (rewrite List.mapMap (List.withIndex row) Pair.fst (((c, cell)) => ((s, c), cell)) in columnsDistinct s 0 row)
        (rowsDistinct (Succ s) rest)
        (List.allOfMem (q => q ∉ List.map later Pair.fst) (List.map (rowCells s row) Pair.fst) (q inRow inLater =>
          Exists.elim (List.memMapElim Pair.fst q (rowCells s row) inRow) (cell both =>
            let atRow: s = q.fst := rewrite <- And.right both in Eq.sym (rowCellsRow s row cell (And.left both))
            let below := rowsAbove (Succ s) rest q inLater
            omega)))

-- Row r's cells are in row r.
theorem rowCellsRow (r: Nat) (row: List a) (cell: ((Nat, Nat), a)) (member: cell ∈ rowCells r row): cell.fst.fst = r :=
  Exists.elim (List.memMapElim (((c, x)) => ((r, c), x)) cell (List.withIndex row) member) (p both =>
    rewrite <- And.right both in rfl)

-- The cells of rows s, s + 1, … are in row s or below.
theorem rowsAbove (s: Nat) (rows: List (List a)) (q: (Nat, Nat))
    (member: q ∈ List.map (List.concat (List.map (List.withIndexFrom s rows) (p => rowCells p.fst p.snd))) Pair.fst): s ≤ q.fst :=
  Exists.elim (List.memMapElim Pair.fst q _ member) (cell both =>
    List.anyElim (p => cell ∈ rowCells p.fst p.snd) (s ≤ q.fst) (List.withIndexFrom s rows)
      (List.memFlatMapElim (p => rowCells p.fst p.snd) cell (List.withIndexFrom s rows) (And.left both))
      (p inRows inRow =>
        let above := indexFromAbove s rows p inRows
        let atRow := rowCellsRow p.fst p.snd cell inRow
        let same: cell.fst = q := And.right both
        rewrite <- same in omega))

-- Every index of `withIndexFrom t` is t or more.
theorem indexFromAbove: (t: Nat) → (xs: List a) → (p: (Nat, a)) → p ∈ List.withIndexFrom t xs → t ≤ p.fst
  | t, Nil, p, member => Void.exfalso member
  | t, Cons x rest, p, Inl same => rewrite <- same in Nat.leRefl t
  | t, Cons x rest, p, Inr later =>
    let above := indexFromAbove (Succ t) rest p later
    omega

-- A row's positions, (s, t), (s, t + 1), …: no repeats.
theorem columnsDistinct (s: Nat): (t: Nat) → (xs: List a) → List.Distinct (List.map (List.withIndexFrom t xs) (p => (s, p.fst)))
  | t, Nil => Trivial
  | t, Cons x rest =>
    Both
      (member =>
        Exists.elim (List.memMapElim (p => (s, p.fst)) (s, t) (List.withIndexFrom (Succ t) rest) member) (p both =>
          let above := indexFromAbove (Succ t) rest p (And.left both)
          let same: p.fst = t := Eq.cong Pair.snd (And.right both)
          omega))
      (columnsDistinct s (Succ t) rest)
