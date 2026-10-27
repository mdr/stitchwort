-- `parseGrid` reads the lines as the puzzle does: when it makes a grid, the
-- cell in row r, column c is `parseChar` of line r's character c (`@` is a
-- roll, `.` floor), and floor past the lines (`parseGridCells`).

namespace Aoc.Day04.Proofs
import Aoc.Day04 (..)
import Aoc.Day04.Spec (..)
import Std (Bool, Eq, Fin, List, Nat, Option, Result, Text, Vec, Void)

-- Rows that `traverseOption` accepted, cell by cell.
theorem parsedCell (lines: List Text) (rows: Vec (Vec Cell (Text.length (List.headOr lines ""))) lines.length)
    (ok: Vec.traverseOption (Vec.fromList lines) (line => Vec.ofList (Text.length (List.headOr lines "")) (parseLine line)) = Some rows) (r: Nat) (c: Nat):
    rowsCells rows r c = List.getOr (parseLine (List.getOr lines r "")) c Floor :=
  let width := Text.length (List.headOr lines "")
  match e: Nat.leq (Succ r) lines.length with
    | True =>
      let i := Fin.ofNatLt lines.length r e
      calc rowsCells rows r c
        _ = Vec.getOr (Vec.get rows i) c Floor
          := rewrite <- Vec.getOrGet rows i (Vec.replicate width Floor), Fin.toNatOfNatLt lines.length r e
        _ = List.getOr (parseLine (Vec.get (Vec.fromList lines) i)) c Floor
          := rewrite Vec.ofListToList width (parseLine (Vec.get (Vec.fromList lines) i)) (Vec.get rows i)
            (Vec.traverseOptionGet (line => Vec.ofList width (parseLine line)) (Vec.fromList lines) rows ok i)
        _ = List.getOr (parseLine (List.getOr lines r "")) c Floor
          := rewrite <- Vec.getToList (Vec.fromList lines) i "", Vec.toListFromList lines, Fin.toNatOfNatLt lines.length r e
    | False =>
      let past: lines.length ≤ r := omega
      rewrite rowsCellsBelow rows r c past, List.getOrPast lines r "" past

theorem gridOfCells (lines: List Text) (grid: Grid) (h: gridOf lines = Some grid) (r: Nat) (c: Nat):
    cellsOf grid r c = List.getOr (parseLine (List.getOr lines r "")) c Floor :=
  let width := Text.length (List.headOr lines "")
  let f := (line: Text) => Vec.ofList width (parseLine line)
  let g := (rows: Vec (Vec Cell width) lines.length) => ({ height = lines.length, width, rows }: Grid)
  match e: Vec.traverseOption (Vec.fromList lines) f with
    | None => Void.exfalso (Option.noneNotSome grid h)
    | Some rows =>
      let same: g rows = grid := Eq.cong (.getOrElse (g rows)) h
      rewrite <- same in parsedCell lines rows e r c

theorem parseGridCells (lines: List Text) (grid: Grid) (h: parseGrid lines = Ok grid) (r: Nat) (c: Nat):
    cellsOf grid r c = List.getOr (parseLine (List.getOr lines r "")) c Floor :=
  match e: findStray lines with
    | Some (row, column, ch) => Void.exfalso (Bool.falseNotTrue (Eq.cong Result.isOk h))
    | None => gridOfCells lines grid (Eq.trans (Eq.sym (Result.toOptionToResult _ (gridOf lines))) (Eq.cong Result.toOption h)) r c
