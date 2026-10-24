-- Day 6, proved: the program keeps its promise that a short line reads as
-- ending in spaces. Two worksheets with the same cells (`column` reads a
-- space past a line's end) parse to the same problems
-- (`parseWorksheetSameCells`), so spaces added to the end of any lines change
-- nothing (`parseWorksheetPadded`), however many on each.

namespace Aoc.Day06.Proofs
import Aoc.Day06 (..)
import Aoc.Day06.Spec (..)
import Std (Eq, List, Nat, Text)

-- From column s on, past every line's end, every column is blank.
theorem blankFrom (lines: List Text): (m: Nat) -> (s: Nat) -> gridWidth lines <= s ->
    List.all isBlank ((List.rangeFrom m s).map (column lines)) = True
  | Zero, s, h => rfl
  | Succ m, s, h =>
    rewrite blankPast s lines (r => Nat.leTrans _ _ _ (List.lengthLeMaxLength r (lines.map Text.toList)) h) in
      blankFrom lines m (Succ s) (omega)

-- The blocks, read over any number of columns from the widest line's length on.
theorem blocksOver (lines: List Text) (n: Nat) (h: gridWidth lines <= n):
    blocks lines = List.splitBy isBlank ((List.range n).map (column lines)) :=
  calc blocks lines
    _ = List.splitBy isBlank ((List.range (gridWidth lines)).map (column lines)) := rewrite columnsAre lines
    _ = List.splitBy isBlank ((List.rangeFrom (gridWidth lines + (n - gridWidth lines)) 0).map (column lines))
      := rewrite List.rangeFromAppend (gridWidth lines) (n - gridWidth lines) 0, List.mapAppend (column lines) (List.range (gridWidth lines)) (List.rangeFrom (n - gridWidth lines) (gridWidth lines)) in
        Eq.sym (List.splitByAppendSeparators isBlank _ _ (blankFrom lines (n - gridWidth lines) (gridWidth lines) (Nat.leRefl (gridWidth lines))))
    _ = List.splitBy isBlank ((List.range n).map (column lines)) := rewrite Nat.addSubCancel (gridWidth lines) n h

-- Two worksheets with the same cells, column by column, parse to the same
-- problems, whatever their lines' lengths.
theorem parseWorksheetSameCells (lines: List Text) (other: List Text) (same: (c: Nat) -> column other c = column lines c):
    parseWorksheet other = parseWorksheet lines :=
  rewrite blocksOver other (Nat.max (gridWidth lines) (gridWidth other)) (Nat.leMaxRight (gridWidth lines) (gridWidth other)),
    blocksOver lines (Nat.max (gridWidth lines) (gridWidth other)) (Nat.leMaxLeft (gridWidth lines) (gridWidth other)),
    List.mapCong _ _ (List.range (Nat.max (gridWidth lines) (gridWidth other))) same

-- So spaces on the end of the lines, `spaces line` of them on each, change no
-- problem: a short line reads as ending in spaces.
theorem parseWorksheetPadded (lines: List Text) (spaces: Text -> Nat):
    parseWorksheet (lines.map (line => line ++ Text.fromList (List.replicate (spaces line) ' '))) = parseWorksheet lines :=
  parseWorksheetSameCells lines _ (c =>
    Eq.trans (List.mapMap (line => charAt line c) (line => line ++ Text.fromList (List.replicate (spaces line) ' ')) lines)
      (List.mapCong _ _ lines (line => List.getOrAppendReplicate ' ' (spaces line) c line.toList)))
