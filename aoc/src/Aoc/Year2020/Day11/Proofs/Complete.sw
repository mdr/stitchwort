--| The converse of `Parse.sw`: a layout whose rows are written with `.`, `L`
--| and `#` (and is a rectangle, which `parseLayout` insists on) is what
--| `parseLayout` reads from that text.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Common (Grid, parseGrid)
import Aoc.Common.Proofs (parseGridComplete)
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11.Spec (RowWritten, symbol)
import Std (Bool, DecEq, Eq, Fail, List, NonEmptyList, Parse, Result, Text, Void)

--| The characters a layout is drawn with.
def isSeatChar (char: Char): Bool := char == '.' ∨ char == 'L' ∨ char == '#'

theorem isSeatCharSymbol ∀ (kind: Seat): isSeatChar (symbol kind) = True := match kind with
  | Floor => rfl
  | Empty => rfl
  | Occupied => rfl

theorem runsSeat ∀ (kind: Seat) (rest: List Char) (allowed: isSeatChar (symbol kind) = True): Parse.Runs seat [symbol kind] rest kind :=
  match kind with
    | Floor => Parse.runsPick [] "." Floor [("L", Empty), ("#", Occupied)] rest rfl
    | Empty => Parse.runsPick [(".", Floor)] "L" Empty [("#", Occupied)] rest (Both rfl rfl)
    | Occupied => Parse.runsPick [(".", Floor), ("L", Empty)] "#" Occupied [] rest (Both rfl (Both rfl rfl))

--| A seat's character is not the start of another seat's, where `char` isn't a seat character.
theorem seatAbsent ∀ (first: Char) (char: Char) (more: List Char) (member: isSeatChar first = True) (stops: isSeatChar char = False):
    Text.stripPrefixChars [first] [char, ..more] = None := match same: Text.sameChar first char with
      | True => cases
      | False => rfl

theorem declinesSeat ∀ (input: List Char) (stops: Parse.CannotStart isSeatChar input): Parse.Declines seat input :=
  Parse.declinesPick _ input
    (match input with
      | [] => Both rfl (Both rfl (Both rfl rfl))
      | [char, ..more] =>
        let stop := stops char more rfl
        Both (seatAbsent '.' char more rfl stop) (Both (seatAbsent 'L' char more rfl stop) (Both (seatAbsent '#' char more rfl stop) rfl)))

theorem allSeats ∀ (row: List Seat): (row.map symbol).all isSeatChar = True := match row with
  | [] => rfl
  | [kind, ..more] => rewrite isSeatCharSymbol kind in allSeats more

theorem runsRow ∀ (line: List Char) (row: List Seat) (written: RowWritten line row) (nonEmpty: row ≠ []):
    Parse.Runs (() => Parse.many1 seat |> .toList) line [] row := match row, nonEmpty with
      | [], nonEmpty2 => Void.exfalso (nonEmpty2 rfl)
      | [first, ..more], nonEmpty2 =>
        rewrite written in
          Parse.runsMap (() => Parse.many1 seat) NonEmptyList.toList _ [] (NonEmptyList.cons first more)
            (Parse.runsMany1Symbols seat symbol isSeatChar runsSeat declinesSeat first more [] (allSeats [first, ..more])
              (char more2 found => Void.exfalso (List.consNotNil char more2 (Eq.sym found))))

theorem layoutEta ∀ (layout: Layout): ({ grid = layout.grid }: Layout) = layout := match layout with
  | { grid } => rfl

--| The soundness theorem's conclusion: every line of the input is its row of
--| the layout written out, and the layout is a rectangle.
def InputWritten (input: Text) (layout: Layout): Prop :=
  List.All2 RowWritten (input.lines.map Text.toList) layout.grid.rows ∧ layout.grid.Rectangle

--| Input whose lines are the rows of a rectangular layout written out is read as that layout.
theorem parseComplete ∀ (input: Text) (layout: Layout) (written: InputWritten input layout): Fail.toResult (() => parseLayout input) = Ok layout :=
  match written with
    | Both lines rectangle =>
      let rowsRead: Fail.toResult (() => Parse.eachLine input (() => Parse.many1 seat |> .toList)) = Ok layout.grid.rows :=
        Parse.runsEachLine input (() => Parse.many1 seat |> .toList) layout.grid.rows
          (List.all2WeakenMem _ _ (line row member same =>
            runsRow line row same
              (rowEmpty => layout.grid.widthNonZero (Eq.trans (Eq.sym (rectangle row member)) (rewrite rowEmpty in rfl)))) lines)
      rewrite Fail.toResultThen (() => parseGrid input seat) (grid => ({ grid }: Layout)),
        parseGridComplete input seat layout.grid rectangle rowsRead, layoutEta layout in rfl

--| Soundness (`parseWritten`) is the converse: the input is written as at most one layout.
theorem writtenUnique ∀ (input: Text) (a: Layout) (b: Layout) (writtenA: InputWritten input a) (writtenB: InputWritten input b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))
