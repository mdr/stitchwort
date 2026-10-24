-- Parsing a puzzle input line by line, naming the line that is malformed.

namespace Aoc.Common
import Std (Fail, List, Text)

-- Parses each line with `parse`. A failure says which line it was: "line 3:
-- expected a turn like L68, got 'X12'". Lines are numbered from 1.
def parseLines (parse: Text -> {Fail} a) (lines: List Text): {Fail} (List a) := parseLinesFrom 1 parse lines

-- The same for lines that start at line number `first`: the first of them is
-- "line ${first}".
def parseLinesFrom (first: Nat) (parse: Text -> {Fail} a) (lines: List Text): {Fail} (List a) :=
  List.zip lines (List.rangeFrom lines.length first)
    |> .map (numbered => Fail.context "line ${numbered.snd}" (() => parse numbered.fst))
