-- Tests for the generic range code. Kept apart from the code, so that running a
-- day doesn't check them.

namespace Aoc.Common.Tests
import Aoc.Common (..)
import Std (Fail, List, Parse)

-- One range read from `text`.
def parsed (text: Text): Result Range Text := Fail.toResult (() => Parse.line text range)

test "range" := parsed "3-5" == Ok ({ from = 3, to = 5 })
test "range spaces" := parsed " 3 - 5 " == Ok ({ from = 3, to = 5 })
test "range junk" := parsed "4-x" == Err "column 3: expected a number, got 'x'"
test "range backwards" := parsed "5-3" == Err "column 4: the range 5-3 ends before it starts"
test "contains" := (Range.contains { from = 3, to = 5 } 3, Range.contains { from = 3, to = 5 } 5, Range.contains { from = 3, to = 5 } 6) == (True, True, False)
test "size" := Range.size { from = 3, to = 5 } == 3
test "ids" := Range.ids { from = 3, to = 5 } == [3, 4, 5]
