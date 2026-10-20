-- `parseGrid` reads the lines as the puzzle does: when it makes a grid, the
-- cell in row r, column c is `parseChar` of line r's character c (`@` is a
-- roll, anything else floor), and floor past the lines (`parseGridCells`).

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Std (Eq)

-- Rows that `traverseMaybe` accepted, cell by cell.
theorem parsedCell (lines: List Text) (rows: Vec (Vec Cell (Text.length (List.headOr "" lines))) (List.length lines))
    (ok: Vec.traverseMaybe (line => Vec.ofList (Text.length (List.headOr "" lines)) (parseLine line)) (Vec.fromList lines) = Just rows) (r: Nat) (c: Nat):
    rowsCells rows r c = List.getOr Floor c (parseLine (List.getOr "" r lines)) :=
  let width := Text.length (List.headOr "" lines)
  match e: Nat.leq (Succ r) (List.length lines) with
    | True  =>
      let i := Fin.ofNatLt (List.length lines) r e
      calc rowsCells rows r c
        _ = List.getOr Floor c (Vec.toList (Vec.get rows i))
            := rewrite <- Vec.getToList (Vec.replicate width Floor) rows i, Fin.toNatOfNatLt (List.length lines) r e
        _ = List.getOr Floor c (parseLine (Vec.get (Vec.fromList lines) i))
            := rewrite Vec.ofListToList width (parseLine (Vec.get (Vec.fromList lines) i)) (Vec.get rows i)
                 (Vec.traverseMaybeGet (line => Vec.ofList width (parseLine line)) (Vec.fromList lines) rows ok i)
        _ = List.getOr Floor c (parseLine (List.getOr "" r lines))
            := rewrite <- Vec.getToList "" (Vec.fromList lines) i, Vec.toListFromList lines, Fin.toNatOfNatLt (List.length lines) r e
    | False =>
      let past := Nat.leqFalse (Succ r) (List.length lines) e
      rewrite rowsCellsBelow rows r c past, List.getOrPast "" r lines past

theorem parseGridCells (lines: List Text) (grid: Grid) (h: parseGrid lines = Just grid) (r: Nat) (c: Nat):
    cellsOf grid r c = List.getOr Floor c (parseLine (List.getOr "" r lines)) :=
  let width := Text.length (List.headOr "" lines)
  let f := (line: Text) => Vec.ofList width (parseLine line)
  let g := (rows: Vec (Vec Cell width) (List.length lines)) => ({ height = List.length lines, width, rows }: Grid)
  match e: Vec.traverseMaybe f (Vec.fromList lines) with
    | Nothing   => Void.exfalso (Maybe.nothingNotJust grid h)
    | Just rows =>
      let same: g rows = grid := Eq.cong (Maybe.withDefault (g rows)) h
      rewrite <- same in parsedCell lines rows e r c
