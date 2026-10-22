-- Tests for the generic range code. Kept apart from the code, so that running a
-- day doesn't check them.

namespace Aoc.Common.Tests
import Aoc.Common (..)
import Std (List)

test "parse" := Range.parse "3-5" == Some { from = 3, to = 5 }
test "parse junk" := Range.parse "4-x" == None
test "contains" := (Range.contains { from = 3, to = 5 } 3, Range.contains { from = 3, to = 5 } 5, Range.contains { from = 3, to = 5 } 6) == (True, True, False)
test "size" := Range.size { from = 3, to = 5 } == 3
test "ids" := Range.ids { from = 3, to = 5 } == [3, 4, 5]
