--| The converse of `Parse.sw`: a slice whose rows are written out with `#` and
--| `.` (and is a rectangle, which `parseSlice` insists on) is what
--| `parseSlice` reads from that text.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day17.Proofs
import Aoc.Common (Grid, parseGrid)
import Aoc.Common.Proofs (parseGridComplete)
import Aoc.Year2020.Day17 (..)
import Aoc.Year2020.Day17.Spec (RowWritten, symbol)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, Nat, NonEmptyList, Option, Parse, Result, Text, Void)

--| A character a row of cubes can start with.
def cubeChar (char: Char): Bool := char == '#' ∨ char == '.'

theorem stripDifferent ∀ (first: Char) (others: List Char) (char: Char) (more: List Char)
    (different: (char == first) = False):
    Text.stripPrefixChars [first, ..others] [char, ..more] = None :=
  match e: Text.sameChar first char with
    | False => byComputing
    | True =>
      Void.impossible (different.read (Eq.flipped (DecEq.sound (rewrite Text.sameCharEq first char at e then e))))

theorem runsCube ∀ (state: CubeState) (after: List Char): Parse.Runs cubeState [symbol state] after state :=
  match state with
    | Active => Parse.runsPick [] "#" Active [(".", Inactive)] after byComputing
    | Inactive => Parse.runsPick [("#", Active)] "." Inactive [] after (Both byComputing byComputing)

theorem declinesCube ∀ (rest: List Char) (stops: Parse.CannotStart cubeChar rest): Parse.Declines cubeState rest :=
  Parse.declinesPick _ rest
    (match rest with
      | [] => Both byComputing (Both byComputing byComputing)
      | [char, ..more] =>
        Both
          (stripDifferent '#' [] char more (Bool.orFalseLeft _ _ (stops char more byComputing)))
          (Both (stripDifferent '.' [] char more (Bool.orFalseRight _ _ (stops char more byComputing))) byComputing))

theorem allCubes ∀ (states: List CubeState): (states.map symbol).all cubeChar = True := match states with
  | [] => byComputing
  | [state, ..more] =>
    rewrite allCubes more then
      (match state with
        | Active => byComputing
        | Inactive => byComputing)

theorem runsRow ∀ (line: List Char) (row: List CubeState)
    (written: RowWritten line row)
    (nonEmpty: row ≠ []):
    Parse.Runs (() => Parse.many1 cubeState |> .toList) line [] row :=
  match row, nonEmpty with
    | [], notEmpty => (notEmpty byComputing).impossible
    | [state, ..more], notEmpty =>
      rewrite written then
        Parse.runsMap
          (() => Parse.many1 cubeState)
          NonEmptyList.toList
          ([state, ..more].map symbol)
          []
          (NonEmptyList.cons state more)
          (Parse.runsMany1Symbols cubeState symbol cubeChar
            (state2 after _ => runsCube state2 after)
            declinesCube
            state
            more
            []
            (allCubes [state, ..more])
            (char more2 found => Void.impossible (List.consNotNil char more2 found.flipped)))

--| The soundness theorem's conclusion: every line of the input is its row of the slice written out, and the slice is a rectangle.
def InputWritten (input: Text) (slice2: Slice): Prop :=
  List.All2 RowWritten (input.lines.map Text.toList) slice2.grid.rows ∧ slice2.grid.Rectangle

--| Input whose lines are the rows of a rectangular slice written out is read as that slice.
theorem parseComplete ∀ (input: Text) (slice2: Slice)
    (written: InputWritten input slice2):
    Fail.toResult (() => parseSlice input) = Ok slice2 :=
  match slice2, written with
    | { grid }, Both lines rectangle =>
      let rowsRead: Fail.toResult (() => Parse.eachLine input (() => Parse.many1 cubeState |> .toList))
        = Ok grid.rows :=
        Parse.runsEachLine input
          (() => Parse.many1 cubeState |> .toList)
          grid.rows
          (List.all2WeakenMem _ _
            (line row member same =>
              runsRow line row same (rowEmpty =>
                grid.widthNonZero (Eq.trans (rectangle row member).flipped (rewrite rowEmpty then byComputing))))
            lines)
      let gridRead: Fail.toResult (() => parseGrid input cubeState) = Ok grid :=
        parseGridComplete input cubeState grid rectangle rowsRead
      rewrite Fail.toResultThen (() => parseGrid input cubeState) (grid2 => ({ grid = grid2 }: Slice)) then
        rewrite gridRead then byComputing

--| A slice is written by an input in at most one way, since the parser reads it as one.
theorem writtenUnique ∀ (input: Text) (a b: Slice)
    (writtenA: InputWritten input a)
    (writtenB: InputWritten input b):
    a = b :=
  Result.okInjective (Eq.trans (parseComplete input a writtenA).flipped (parseComplete input b writtenB))
