-- Day 12 as the puzzle states it, over the program's map: its plants
-- (`plantAt`) and a grid point's neighbour in each direction (`step`). The
-- proofs (Proofs/) show the program's regions, perimeters and prices are
-- these, for every map.

namespace Aoc.Year2024.Day12.Spec
import Aoc.Year2024.Day12 (..)
import Std (Bool, Exists, Iff, List, Nat, Option)

-- "Touching (horizontally or vertically)": one column apart in the same
-- row, or one row apart in the same column.
def isOrthogonalStep (from: Position) (to: Position): Bool :=
  (from.row == to.row && (from.column + 1 == to.column || to.column + 1 == from.column))
    || (from.column == to.column && (from.row + 1 == to.row || to.row + 1 == from.row))

-- Two garden plots "growing the same type of plant".
def growSame (garden: Garden) (plot: Position) (other: Position): Bool :=
  match garden.plantAt plot with
    | Some plant => garden.plantAt other == Some plant
    | None => False

-- "When multiple garden plots are growing the same type of plant and are
-- touching (horizontally or vertically), they form a region."
def touches (garden: Garden) (plot: Position) (other: Position): Bool := isOrthogonalStep plot other && growSame garden plot other

-- `chain` leads from `from` to `to`, each plot touching the one before.
def isChain (garden: Garden): (from: Position) → (chain: List Position) → (to: Position) → Bool
  | from, Nil, to => from == to
  | from, Cons next rest, to => touches garden from next && isChain garden next rest to

-- Plots in the same region: joined by a chain of touching plots.
def Joined (garden: Garden) (plot: Position) (other: Position): Prop := Exists (List Position) (chain => isChain garden plot chain other = True)

-- The region containing `plot`, as a list: every plot joined to it is on
-- the list, and nothing else.
def IsRegion (garden: Garden) (plot: Position) (region: List Position): Prop := (other: Position) → Iff (other ∈ region) (Joined garden plot other)

-- Whether the side of `plot` facing `side` touches a plot of the region.
def facesRegion (region: List Position) (plot: Position) (side: Direction): Bool :=
  match plot.step side with
    | Some other => region.any (member => member == other)
    | None => False

-- "The area of a region is simply the number of garden plots the region
-- contains."
def area (region: List Position): Nat := region.length

-- "The perimeter of a region is the number of sides of garden plots in the
-- region that do not touch another garden plot in the same region."
def perimeter (region: List Position): Nat := region.sumBy (plot => directions.count (side => !facesRegion region plot side))

-- A section of fence one plot long: a side of a plot of the region that
-- touches no plot of the region.
def isFence (region: List Position) (plot: Position) (side: Direction): Bool := region.any (member => member == plot) && !facesRegion region plot side

-- The plot before `plot` along a fence on its `side`: left of it for a fence
-- above or below, above it for a fence on the left or right.
def alongBefore (plot: Position) (side: Direction): Option Position :=
  match side with
    | Up => plot.step Left
    | Down => plot.step Left
    | Left => plot.step Up
    | Right => plot.step Up

-- "Each straight section of fence counts as a side, regardless of how long
-- it is": a run of fence facing the same way, plot after plot along a line.
-- Each side is counted once, at its first section, the one with no fence
-- before it along the line.
def isFirstSection (region: List Position) (plot: Position) (side: Direction): Bool :=
  isFence region plot side && !(alongBefore plot side |> .map (before => isFence region before side) |> .getOrElse False)

def sides (region: List Position): Nat := region.sumBy (plot => directions.count (isFirstSection region plot))

-- "The total price of fencing all regions on a map is found by adding
-- together the price of fence for every region on the map", the price being
-- area times perimeter (part 1) or area times sides (part 2).
def totalPrice (regions: List (List Position)) (measure: List Position → Nat): Nat := regions.sumBy (region => area region * measure region)
