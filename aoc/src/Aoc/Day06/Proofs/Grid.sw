-- Day 6, proved: padding makes the grid rectangular, the columns lose nothing,
-- and the blocks are exactly the runs of columns that aren't blank, for any
-- input. Kept apart from the program, so `stitchwort run Aoc.Day06.main`
-- doesn't check it.

namespace Aoc.Day06.Proofs
import Aoc.Day06 (..)

-- Every line is at most this wide (proof-only).
def Fits (width: Nat): List Text -> Prop
  | Nil         => Unit
  | Cons l rest => And (l.length <= width) (Fits width rest)

theorem foldWidenGrows (start: Nat): (lines: List Text) -> start <= lines.foldLeft widen start
  | Nil         => Nat.leRefl start
  | Cons l rest =>
    calc start
      _ <= widen start l                         := Nat.leMaxLeft start l.length
      _ <= rest.foldLeft widen (widen start l)   := foldWidenGrows (widen start l) rest

theorem foldWidenFits (start: Nat): (lines: List Text) -> Fits (lines.foldLeft widen start) lines
  | Nil         => Trivial
  | Cons l rest =>
    Both (calc l.length
            _ <= widen start l                       := Nat.leMaxRight start l.length
            _ <= rest.foldLeft widen (widen start l) := foldWidenGrows (widen start l) rest)
         (foldWidenFits (widen start l) rest)

theorem paddedAllLength (width: Nat): (lines: List Text) -> Fits width lines ->
    List.AllLength width (lines.map (line => line.toList.padRight width ' '))
  | Nil,         fits          => Trivial
  | Cons l rest, Both fit fits => Both (List.padRightLength width ' ' l.toList fit) (paddedAllLength width rest fits)

-- Padding makes the grid rectangular, whatever the input.
theorem paddedGridRectangular (lines: List Text): List.AllLength (gridWidth lines) (paddedGrid lines) :=
  paddedAllLength (gridWidth lines) lines (foldWidenFits 0 lines)

-- So the columns lose nothing: a grid with some width has columns that
-- transpose back to the grid, for any input.
theorem columnsKeepEveryCell (lines: List Text) (w: Nat) (wide: gridWidth lines = Succ w):
    (paddedGrid lines).transpose.transpose = paddedGrid lines :=
  List.transposeTwice w (paddedGrid lines)
    (rewrite <- wide in paddedGridRectangular lines)

-- Only the blank columns separate problems. Every block is a non-empty run of
-- columns with no blank one in it (`isBlank` is the separator test)...
theorem blocksAreRuns (lines: List Text): List.Groups isBlank (blocks lines) :=
  List.splitByGroups isBlank (paddedGrid lines).transpose

-- ...and together the blocks hold every column that isn't blank, in order.
theorem blocksKeepEveryColumn (lines: List Text):
    List.concat (blocks lines) = (paddedGrid lines).transpose.filter (column => not (isBlank column)) :=
  List.splitByConcat isBlank (paddedGrid lines).transpose
