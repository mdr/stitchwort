-- The library's `Vec` (std/Vec/Vec.sw, docs/proposals/vec.md): a grid that
-- is rectangular by its type, parsed from lines of unknown length, and two
-- proofs that go through the library's lemmas.

import Std (Eq)

type Grid = { height: Nat, width: Nat, rows: Vec (Vec Bool width) height }

def parseLine (line: Text): List Bool := line.toList.map (c => c == '#')

-- `None` when a line's length differs from the first's.
def parseGrid (lines: List Text): Option Grid :=
  let width := (lines.headOr "").length
  Vec.fromList lines
    |> Vec.traverseOption (line => Vec.ofList width (parseLine line))
    |> Option.map (rows => ({ height = lines.length, width, rows }: Grid))

def Grid.count (grid: Grid): Nat := grid.rows.sumBy (row => row.sumBy Bool.toNat)

-- No bound checks: the indices' types say they are on the grid.
def Grid.cell (grid: Grid) (r: Fin grid.height) (c: Fin grid.width): Bool := (grid.rows.get r).get c

-- Every cell flipped.
def Grid.flip (grid: Grid): Grid := { grid | rows = grid.rows.map (row => row.map not) }

theorem flipCell (grid: Grid) (r: Fin grid.height) (c: Fin grid.width):
    grid.flip.cell r c = not (grid.cell r c) :=
  calc Vec.get (Vec.get (Vec.map (row => Vec.map not row) grid.rows) r) c
    _ = Vec.get (Vec.map not (Vec.get grid.rows r)) c := Eq.cong (row => Vec.get row c) (Vec.getMap (row => Vec.map not row) grid.rows r)
    _ = not (Vec.get (Vec.get grid.rows r) c)          := Vec.getMap not (Vec.get grid.rows r) c

-- A sum over a vector is the sum over its list, so the list lemmas apply.
theorem sumByMap (f: b -> Nat) (g: a -> b) (v: Vec a n): Vec.sumBy f (Vec.map g v) = List.sumBy f (List.map g (Vec.toList v)) :=
  Eq.trans (Vec.sumByToList f (Vec.map g v)) (Eq.cong (List.sumBy f) (Vec.toListMap g v))

def lines: List Text := [".#.", "###", ".#."]

test "parse and count" := Option.map Grid.count (parseGrid lines) == Some 5
test "flip" := Option.map (g => g.flip.count) (parseGrid lines) == Some 4
test "ragged" := Option.map Grid.count (parseGrid [".#.", "#"]) == None
-- A grid of known size: `getLt` takes a `Nat` index, its bound decided by `auto`.
def plus: Vec (Vec Bool 3) 3 :=
  Vec.fromList [Vec.fromList [False, True, False], Vec.fromList [True, True, True], Vec.fromList [False, True, False]]

test "cell" := Vec.getLt (Vec.getLt plus 1) 2 && not (Vec.getLt (Vec.getLt plus 2) 0)
