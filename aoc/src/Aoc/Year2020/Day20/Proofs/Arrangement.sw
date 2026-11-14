--| What the assembly guarantees by construction: in every row, each tile's
--| left edge is the right edge of the tile before it, and down the first
--| column each tile's top edge is the bottom edge of the one above; every
--| placed tile is an orientation of an input tile other than its
--| neighbour. That the other columns line up, and that each tile is used
--| once, rest on the puzzle's promise that edges match uniquely, and are
--| not proved.

namespace Aoc.Year2020.Day20.Proofs
import Aoc.Year2020.Day20 (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Void)

--| Each tile's left edge is the right edge of the tile before it.
def RowFits: (row: List Tile) → Prop
  | [] => Unit
  | [only] => Unit
  | [first, second, ..rest] => second.image.left = first.image.right ∧ RowFits [second, ..rest]

--| Each row's first tile's top edge is the bottom edge of the first tile
--| of the row above.
def ColumnFits: (rows: List (List Tile)) → Prop
  | [[above, ..restAbove], [below, ..restBelow], ..rest] =>
    below.image.top = above.image.bottom ∧ ColumnFits [[below, ..restBelow], ..rest]
  | other => Unit

--| A tile the jigsaw has, turned, with another id than `tile`.
def TurnedOther (jigsaw: Jigsaw) (tile placed: Tile): Prop :=
  ∃ (original: Tile) => original ∈ jigsaw.tiles ∧ original.id ≠ tile.id ∧ placed ∈ original.orientations

theorem neighbourFound ∀ (jigsaw: Jigsaw) (tile: Tile) (edge: Edge) (placed: Tile → Bool) (next: Tile)
    (found: jigsaw.neighbour tile edge placed = Some next):
    placed next = True ∧ TurnedOther jigsaw tile next :=
  let candidates := jigsaw.tiles.filter (other => other.id != tile.id && other.image.edges.any edge.fits)
  match List.findSome (candidates.flatMap (.orientations)) placed next found with
    | Both fits member =>
      match (List.memFlatMap (.orientations) next candidates).forward member with
        | Witness original (Both candidate turned) =>
          match List.memFilter jigsaw.tiles
            (other => other.id != tile.id && other.image.edges.any edge.fits)
            candidate with
            | Both inTiles kept =>
              let Both different _ := kept
              Both fits (Witness original (Both inTiles (Both different.read.read turned)))

theorem rightOfFits ∀ (jigsaw: Jigsaw) (tile next: Tile)
    (found: jigsaw.rightOf tile = Some next):
    next.image.left = tile.image.right ∧ TurnedOther jigsaw tile next :=
  match neighbourFound jigsaw tile tile.image.right (next => next.image.left == tile.image.right) next found with
    | Both fits turned => Both fits.read turned

theorem belowFits ∀ (jigsaw: Jigsaw) (tile next: Tile)
    (found: jigsaw.below tile = Some next):
    next.image.top = tile.image.bottom ∧ TurnedOther jigsaw tile next :=
  match neighbourFound jigsaw tile tile.image.bottom (next => next.image.top == tile.image.bottom) next found with
    | Both fits turned => Both fits.read turned

theorem rowAfterFits ∀ (jigsaw: Jigsaw) (tile: Tile) (fuel: Nat): RowFits [tile, ..jigsaw.rowAfter tile fuel] :=
  match fuel with
    | Zero => Trivial
    | Succ fuel =>
      match found: jigsaw.rightOf tile with
        | None => Trivial
        | Some next => Both (rightOfFits jigsaw tile next found).left (rowAfterFits jigsaw next fuel)

--| From any first tile (`arrange` starts from `topLeft`), every row fits
--| edge to edge, and so does the first column.
theorem rowsFromFits ∀ (jigsaw: Jigsaw) (first: Tile) (fuel: Nat):
    (∀ (row: List Tile) => row ∈ jigsaw.rowsFrom first fuel → RowFits row) ∧ ColumnFits (jigsaw.rowsFrom first fuel) :=
  match fuel with
    | Zero => Both (row member => Void.exfalso member) Trivial
    | Succ fuel =>
      let firstRow := rowAfterFits jigsaw first jigsaw.tiles.length
      match found: jigsaw.below first with
        | None =>
          Both
            (row member =>
              match member with
                | Inl same => rewrite <- same in firstRow
                | Inr never => Void.exfalso never)
            Trivial
        | Some next =>
          let later := rowsFromFits jigsaw next fuel
          Both
            (row member =>
              match member with
                | Inl same => rewrite <- same in firstRow
                | Inr more => later.left row more)
            (match fuel with
              | Zero => Trivial
              | Succ more => Both (belowFits jigsaw first next found).left later.right)
