-- Advent of Code 2025, day 5's input read with `Std.Parse`: ranges of ids
-- ("3-5"), one per line, a blank line, then ids, one per line. The whole
-- input is one grammar, so line numbers run through both sections.
--
--   3-5
--   10-14
--
--   1
--   5
import Std (Fail, List, Nat, Parse, Result, Text)
import Std.Fail (toResult)
import Std.Parse (blankLine, char, lines, nat, spaces)

-- A range of ids, both ends included.
type Range = { from: Nat, to: Nat }

type Database = { fresh: List Range, available: List Nat }

-- A number, with spaces allowed around it.
def spacedNat(): {Parse} Nat :=
  spaces()
  let number := nat()
  spaces()
  number

-- "11-22", or " 11 - 22 ". A range that ends before it starts fails where
-- the parse has got to: the end of the range.
def range(): {Parse} Range :=
  let from := spacedNat()
  char '-'
  let to := spacedNat()
  Parse.ensure (from ≤ to) "the range ends before it starts"
  { from, to }

def database(): {Parse} Database :=
  let fresh := lines range
  blankLine()
  let available := lines spacedNat
  { fresh, available }

def parseDatabase (input: Text): {Fail} Database := Parse.all input database

test "database" := toResult (() => parseDatabase "3-5\n10-14\n\n1\n5\n") ==
  Ok ({ fresh = [{ from = 3, to = 5 }, { from = 10, to = 14 }], available = [1, 5] }: Database)
test "spaces around numbers" := toResult (() => parseDatabase " 3 - 5 \n\n 1 \n") ==
  Ok ({ fresh = [{ from = 3, to = 5 }], available = [1] }: Database)
test "a bad id" := toResult (() => parseDatabase "3-5\n10-14\n\n1\nx\n") == Err "line 5, column 1: expected a number or the end"
test "a bad range" := toResult (() => parseDatabase "3-5\n10x14\n\n1\n") == Err "line 2, column 3: expected '-'"
test "a backwards range" := toResult (() => parseDatabase "5-3\n\n1\n") == Err "line 1, column 4: the range ends before it starts"
test "no blank line" := toResult (() => parseDatabase "3-5\n1\n") == Err "line 2, column 2: expected '-'"
