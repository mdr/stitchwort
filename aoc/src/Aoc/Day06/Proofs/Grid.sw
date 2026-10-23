-- Day 6, proved: the columns are rectangular and lose nothing, and the blocks
-- are exactly the runs of columns that aren't blank, for any input. Kept
-- apart from the program, so `stitchwort run Aoc.Day06.main` doesn't check
-- it.

namespace Aoc.Day06.Proofs
import Aoc.Day06 (..)
import Aoc.Day06.Spec (..)
import Std (Char, List, Nat, Text)

-- Every column has a cell for every line, whatever the input.
theorem columnsRectangular (lines: List Text) (c: Nat) (h: c < gridWidth lines):
    List.length (List.getOr Nil c ((lines.map Text.toList).transposeFill ' ')) = lines.length :=
  rewrite List.lengthColumnTransposeFill ' ' (lines.map Text.toList) c h in List.lengthMap Text.toList lines

-- So the columns lose nothing: a grid with some width has columns that
-- transpose back to every line, cell by cell, for any input.
theorem columnsKeepEveryCell (lines: List Text) (w: Nat) (wide: gridWidth lines = Succ w):
    ((lines.map Text.toList).transposeFill ' ').transpose = lines.map (line => (List.range (gridWidth lines)).map (charAt line)) :=
  rewrite columnsAre lines, wide in List.transposeGrid (c line => charAt line c) 0 (List.rangeFrom w 1) lines

-- Only the blank columns separate problems. Every block is a non-empty run of
-- columns with no blank one in it (`isBlank` is the separator test)...
theorem blocksAreRuns (lines: List Text): List.Groups isBlank (blocks lines) :=
  List.splitByGroups isBlank ((lines.map Text.toList).transposeFill ' ')

-- ...and together the blocks hold every column that isn't blank, in order.
theorem blocksKeepEveryColumn (lines: List Text):
    List.concat (blocks lines) = ((lines.map Text.toList).transposeFill ' ').filter (column => not (isBlank column)) :=
  List.splitByConcat isBlank ((lines.map Text.toList).transposeFill ' ')

-- Why `readNumber` is the right reading: a number written in decimal, with
-- any spaces before and after it (its alignment in the problem), reads back
-- as itself.
theorem spacesNoDigits: (k: Nat) -> List.filterMap Char.digitValue (List.replicate k ' ') = Nil
  | Zero => rfl
  | Succ k => spacesNoDigits k

theorem readNumberWritten (n: Nat) (before: Nat) (after: Nat):
    readNumber (List.append (List.replicate before ' ') (List.append (Text.toList (Nat.toText n)) (List.replicate after ' '))) = n :=
  rewrite List.filterMapAppend Char.digitValue (List.replicate before ' ') (List.append (Text.toList (Nat.toText n)) (List.replicate after ' ')),
    List.filterMapAppend Char.digitValue (Text.toList (Nat.toText n)) (List.replicate after ' '),
    spacesNoDigits before, spacesNoDigits after, Char.toTextDigits n, List.appendNil (Nat.digits n) in
      Nat.fromDigitsDigits n
