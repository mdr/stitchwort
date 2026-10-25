-- Parsing a puzzle input line by line, naming the line that is malformed.

namespace Aoc.Common
import Std (Fail, List, Text)

-- Parses each line with `parse`. A failure says which line it was: "line 3:
-- expected a turn like L68, got 'X12'". Lines are numbered from 1.
def parseLines (lines: List Text) (parse: Text → {Fail} a): {Fail} (List a) := parseLinesFrom lines 1 parse

-- The same for lines that start at line number `first`: the first of them is
-- "line ${first}".
def parseLinesFrom (lines: List Text) (first: Nat) (parse: Text → {Fail} a): {Fail} (List a) :=
  List.zip lines (List.rangeFrom lines.length first)
    |> .map (numbered => Fail.context "line ${numbered.snd}" (() => parse numbered.fst))
