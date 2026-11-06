--| Tests for the shared elimination.

namespace Aoc.Common.Tests
import Aoc.Common (..)
import Std (List, Nat, Option, Text)

test "assign settles a position at a time" := assign [["a", "b"], ["a"], ["b", "c"]] == Some ["b", "a", "c"]
test "assign settles an allergen at a time" :=
  assign [["mxmxvkd"], ["mxmxvkd", "sqjhc"], ["sqjhc", "fvjkl"]] == Some ["mxmxvkd", "sqjhc", "fvjkl"]
test "assign stops where every position has two candidates" := assign [[1, 2], [1, 2]] == (None: Option (List Nat))
test "assign stops at a position with no candidates" := assign [[1], []] == (None: Option (List Nat))
test "assign of no positions is empty" := assign ([]: List (List Nat)) == Some []
