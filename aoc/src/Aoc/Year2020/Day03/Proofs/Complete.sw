--| The converse of `Parse.sw`: a map whose rows are written with `.` and `#`
--| (and is a rectangle, which `parseMap` insists on) is what `parseMap` reads
--| from that text.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day03.Proofs
import Aoc.Common (Grid)
import Aoc.Common.Proofs (parseGridComplete)
import Aoc.Year2020.Day03 (..)
import Std (Eq, Fail, List, NonEmptyList, Parse, Result, Text, Void)

theorem ofCharSymbol ∀ (square: Square): Square.ofChar (symbol square) = square := match square with
  | Open => rfl
  | Tree => rfl

theorem isSquareSymbol ∀ (square: Square): isSquare (symbol square) = True := match square with
  | Open => rfl
  | Tree => rfl

theorem runsSquare ∀ (kind: Square) (rest: List Char)
    (allowed: isSquare (symbol kind) = True):
    Parse.Runs square [symbol kind] rest kind :=
  let runs :=
    Parse.runsMap
      (() => Parse.satisfy "'.' or '#'" isSquare)
      Square.ofChar
      [symbol kind]
      rest
      (symbol kind)
      (Parse.runsSatisfy _ _ (symbol kind) rest allowed)
  rewrite ofCharSymbol kind at runs in runs

theorem declinesSquare ∀ (input: List Char) (stops: Parse.CannotStart isSquare input): Parse.Declines square input :=
  Parse.declinesBind
    (() => Parse.satisfy "'.' or '#'" isSquare)
    Square.ofChar
    input
    (match input with
      | [] => Parse.declinesSatisfyEnd _ _
      | [char, ..more] => Parse.declinesSatisfy _ _ char more (stops char more rfl))

theorem allSquares ∀ (row: List Square): (row.map symbol).all isSquare = True := match row with
  | [] => rfl
  | [kind, ..more] => rewrite isSquareSymbol kind in allSquares more

theorem runsRow ∀ (line: List Char) (row: List Square)
    (written: line = row.map symbol)
    (nonEmpty: row ≠ []):
    Parse.Runs (() => Parse.many1 square |> .toList) line [] row :=
  match row, nonEmpty with
    | [], nonEmpty2 => Void.exfalso (nonEmpty2 rfl)
    | [first, ..more], nonEmpty2 =>
      rewrite written in
        Parse.runsMap
          (() => Parse.many1 square)
          NonEmptyList.toList _
          []
          (NonEmptyList.cons first more)
          (Parse.runsMany1Symbols square symbol isSquare runsSquare declinesSquare first more []
            (allSquares [first, ..more])
            (char more2 found => Void.exfalso (List.consNotNil char more2 (Eq.sym found))))

--| The soundness theorem's conclusion for a rectangle, which `parseMap` insists on: every
--| line of the input is its row of the map written out.
def InputWritten (input: Text) (map: Grid Square): Prop :=
  List.All2 (line row => line = row.map symbol) (input.lines.map Text.toList) map.rows ∧ map.Rectangle

--| Input whose lines are the rows of a rectangular map written out is read as that map.
theorem parseComplete ∀ (input: Text) (map: Grid Square)
    (written: InputWritten input map):
    Fail.toResult (() => parseMap input) = Ok map :=
  match written with
    | Both lines rectangle =>
      let rowsRead: Fail.toResult (() => Parse.eachLine input (() => Parse.many1 square |> .toList)) = Ok map.rows :=
        Parse.runsEachLine input
          (() => Parse.many1 square |> .toList)
          map.rows
          (List.all2WeakenMem _ _
            (line row member same =>
              runsRow line row same (rowEmpty =>
                map.widthNonZero (Eq.trans (Eq.sym (rectangle row member)) (rewrite rowEmpty in rfl))))
            lines)
      parseGridComplete input square map rectangle rowsRead

--| Soundness (`parseWritten`) is the converse: the input is written as at most one map.
theorem writtenUnique ∀ (input: Text) (a b: Grid Square)
    (writtenA: InputWritten input a)
    (writtenB: InputWritten input b):
    a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
