-- Tests for the generic range code. Kept apart from the code, so that running a
-- day doesn't check them.

namespace Aoc.Common.Tests
import Aoc.Common (..)
import Std (Fail, List)

test "parse" := Range.parse "3-5" == Some ({ from = 3, to = 5 })
test "parse junk" := Range.parse "4-x" == None
test "read spaces" := Fail.toResult (() => Range.read " 3 - 5 ") == Ok ({ from = 3, to = 5 })
test "read junk" := Fail.toResult (() => Range.read "4-x") == Err "expected a range like 11-22, got '4-x'"
test "contains" := (Range.contains { from = 3, to = 5 } 3, Range.contains { from = 3, to = 5 } 5, Range.contains { from = 3, to = 5 } 6) == (True, True, False)
test "size" := Range.size { from = 3, to = 5 } == 3
test "ids" := Range.ids { from = 3, to = 5 } == [3, 4, 5]
