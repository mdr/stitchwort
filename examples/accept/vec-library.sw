-- The library's `Vec` (std/Vec/Vec.sw, docs/proposals/vec.md): a grid that
-- is rectangular by its type, parsed from lines of unknown length, and two
-- proofs that go through the library's lemmas.

import Std (Bool, Eq, Fin, List, Option, Vec)

type Grid = { height: Nat, width: Nat, rows: Vec (Vec Bool width) height }

def parseLine (line: Text): List Bool := line.toList.map (== '#')

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
  calc Vec.get (Vec.get (Vec.map grid.rows (row => Vec.map row not)) r) c
    _ = Vec.get (Vec.map (Vec.get grid.rows r) not) c := Eq.cong (row => Vec.get row c) (Vec.getMap grid.rows r (row => Vec.map row not))
    _ = not (Vec.get (Vec.get grid.rows r) c) := Vec.getMap (Vec.get grid.rows r) c not

-- A sum over a vector is the sum over its list, so the list lemmas apply.
theorem sumByMap (f: b -> Nat) (g: a -> b) (v: Vec a n): Vec.sumBy (Vec.map v g) f = List.sumBy (List.map (Vec.toList v) g) f :=
  Eq.trans (Vec.sumByToList (Vec.map v g) f) (Eq.cong (.sumBy f) (Vec.toListMap v g))

def lines: List Text := [".#.", "###", ".#."]

test "parse and count" := Option.map (parseGrid lines) Grid.count == Some 5
test "flip" := Option.map (parseGrid lines) (g => g.flip.count) == Some 4
test "ragged" := Option.map (parseGrid [".#.", "#"]) Grid.count == None
-- A grid of known size: `getLt` takes a `Nat` index, its bound decided by `auto`.
def plus: Vec (Vec Bool 3) 3 :=
  Vec.fromList [Vec.fromList [False, True, False], Vec.fromList [True, True, True], Vec.fromList [False, True, False]]

test "cell" := Vec.getLt (Vec.getLt plus 1) 2 && not (Vec.getLt (Vec.getLt plus 2) 0)
