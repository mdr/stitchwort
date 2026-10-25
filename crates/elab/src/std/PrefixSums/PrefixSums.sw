-- Sums over blocks of a grid of numbers, each in O(log n) once the grid has
-- been read in O(n log n): a summed-area table, or 2D prefix sums (Python's
-- `numpy.cumsum` along both axes, then four lookups). `PrefixSums.of rows`
-- reads the grid, rows of any lengths, a missing cell counting as 0, and
-- `PrefixSums.block` sums a block of it. The theorem at the bottom says the
-- block is the sum of its cells (`PrefixSums.blockSum`).

-- The table: entry (r, c) is the sum of the cells above row r and left of
-- column c, for r up to the number of rows and c up to the longest row's
-- length, kept for lookup by position.
type PrefixSums = { sums: Map Nat (Map Nat Nat) }

-- The cells of rows of numbers, row r and column c; 0 outside them.
def PrefixSums.cell (rows: List (List Nat)) (r: Nat) (c: Nat): Nat := List.getOr (List.getOr rows Nil r) 0 c

-- The sum of the block of rows `top` up to, not including, `bottom`, and
-- columns `left` up to, not including, `right`, cell by cell: what
-- `PrefixSums.block` computes in four lookups.
def PrefixSums.blockSpec (rows: List (List Nat)) (top: Nat) (bottom: Nat) (left: Nat) (right: Nat): Nat :=
  List.sumBy (List.rangeFrom (bottom - top) top) (r => List.sumBy (List.rangeFrom (right - left) left) (c => PrefixSums.cell rows r c))

-- Reads the grid.
def PrefixSums.of (rows: List (List Nat)): PrefixSums :=
  let width := List.maxLength rows
  let table := PrefixSums.table (List.replicate (Succ width) 0) (List.map rows (row => PrefixSums.runningSums (List.padRight row width 0)))
  { sums = Map.byPosition (List.map table Map.byPosition) }

-- The running sums of a row, from 0: `[2, 3]` gives `[0, 2, 5]`.
def PrefixSums.runningSums (row: List Nat): List Nat := List.scanLeft row 0 Nat.add

-- The table's rows from the running sums of each row: `above` is the row of
-- the table for the rows before.
def PrefixSums.table (above: List Nat): List (List Nat) -> List (List Nat)
  | Nil => [above]
  | Cons sums rest => Cons above (PrefixSums.table (List.zipWith above sums Nat.add) rest)

-- Entry (r, c) of the table.
def PrefixSums.at (prefix: PrefixSums) (r: Nat) (c: Nat): Nat := Map.getOr (Map.getOr prefix.sums Map.empty r) 0 c

-- The sum of the cells of rows `top` up to, not including, `bottom`, and
-- columns `left` up to, not including, `right`. Inside the grid (`bottom` at
-- most the number of rows, `right` at most the longest row's length), that
-- is `PrefixSums.blockSpec`.
def PrefixSums.block (prefix: PrefixSums) (top: Nat) (bottom: Nat) (left: Nat) (right: Nat): Nat :=
  (prefix.at bottom right + prefix.at top left) - (prefix.at top right + prefix.at bottom left)

def PrefixSums.example: List (List Nat) := [[1, 2, 3], [4, 5], [7, 8, 9]]

test "PrefixSums.block" :=
  (PrefixSums.of PrefixSums.example).block 0 3 0 3 == 39
    && (PrefixSums.of PrefixSums.example).block 1 3 1 3 == 22
    && (PrefixSums.of PrefixSums.example).block 1 2 2 3 == 0
    && (PrefixSums.of PrefixSums.example).block 2 2 0 3 == 0
test "PrefixSums.blockSpec" := PrefixSums.blockSpec PrefixSums.example 1 3 1 3 == 22
test "PrefixSums.table" := PrefixSums.table [0, 0] [[0, 1], [0, 2]] == [[0, 0], [0, 1], [0, 3]]
test "PrefixSums of no rows" := (PrefixSums.of Nil).block 0 0 0 0 == 0
