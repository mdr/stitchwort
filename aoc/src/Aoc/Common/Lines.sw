-- Reading a puzzle input line by line, naming the line that is malformed.

namespace Aoc.Common
import Std (Fail, List, Text)

-- Reads each line with `read`. A failure says which line it was: "line 3:
-- expected a turn like L68, got 'X12'". Lines are numbered from 1.
def readLines (read: Text -> {Fail} a) (lines: List Text): {Fail} (List a) := readLinesFrom 1 read lines

-- The same for lines that start at line number `first`: the first of them is
-- "line ${first}".
def readLinesFrom (first: Nat) (read: Text -> {Fail} a) (lines: List Text): {Fail} (List a) :=
  List.zip lines (List.rangeFrom lines.length first)
    |> .mapIn (numbered => Fail.context "line ${numbered.snd}" (() => read numbered.fst))
