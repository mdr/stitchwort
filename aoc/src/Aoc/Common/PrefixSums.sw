--| Sums over blocks of a grid of numbers, each in O(log n) once the grid has
--| been read in O(n log n): a summed-area table, or 2D prefix sums (Python's
--| `numpy.cumsum` along both axes, then four lookups). `PrefixSums.of rows`
--| reads the grid, rows of any lengths, a missing cell counting as 0, and
--| `PrefixSums.block` sums a block of it. The theorem in `Proofs/PrefixSums.sw`
--| says the block is the sum of its cells (`PrefixSums.blockSum`).

namespace Aoc.Common
import Std (List, Map, Nat)

--| The table of prefix sums, kept for lookup by position.
--| Entry (r, c) is the sum of the cells above row r and left of column c, for
--| r up to the number of rows and c up to the longest row's length.
type PrefixSums = { sums: Map Nat (Map Nat Nat) }

--| The cells of rows of numbers, row r and column c; 0 outside them.
def PrefixSums.cell (rows: List (List Nat)) (r c: Nat): Nat := rows.getOr r [] |> .getOr c 0

--| The sum of a block of cells, added cell by cell: what `PrefixSums.block` computes in four lookups.
--| The block is rows `top` up to, not including, `bottom`, and columns `left`
--| up to, not including, `right`.
def PrefixSums.blockSpec (rows: List (List Nat)) (top bottom left right: Nat): Nat :=
  List.sumBy (List.rangeFrom (bottom - top) top) (r =>
    List.sumBy (List.rangeFrom (right - left) left) (c => PrefixSums.cell rows r c))

--| The prefix sums of a grid of numbers, rows of any lengths, a missing cell counting as 0: O(n log n).
def PrefixSums.of (rows: List (List Nat)): PrefixSums :=
  let width := List.maxLength rows
  let table :=
    PrefixSums.table (List.replicate (Succ width) 0) (rows.map (row => PrefixSums.runningSums (row.padRight width 0)))
  { sums = table.map Map.byPosition |> Map.byPosition }

--| The running sums of a row, from 0: `[2, 3]` gives `[0, 2, 5]`.
def PrefixSums.runningSums (row: List Nat): List Nat := List.scanLeft row 0 Nat.add

--| The table's rows from the running sums of each row: `above` is the row of
--| the table for the rows before.
def PrefixSums.table (above: List Nat): (rows: List (List Nat)) → List (List Nat)
  | [] => [above]
  | [sums, ..rest] => [above, ..PrefixSums.table (List.zipWith above sums Nat.add) rest]

--| Entry (r, c) of the table.
def PrefixSums.at (prefix: PrefixSums) (r c: Nat): Nat := prefix.sums.getOr r Map.empty |> .getOr c 0

--| The sum of the cells of rows `top` up to, not including, `bottom`, and
--| columns `left` up to, not including, `right`. Inside the grid (`bottom` at
--| most the number of rows, `right` at most the longest row's length), that
--| is `PrefixSums.blockSpec`.
def PrefixSums.block (prefix: PrefixSums) (top bottom left right: Nat): Nat :=
  (prefix.at bottom right + prefix.at top left) - (prefix.at top right + prefix.at bottom left)
