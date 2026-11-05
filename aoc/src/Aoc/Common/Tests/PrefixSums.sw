--| Tests for the shared prefix-sums code.

namespace Aoc.Common.Tests
import Aoc.Common (..)
import Std (List, Nat)

--| A small grid of rows of different lengths for the tests below.
def PrefixSums.example: List (List Nat) := [[1, 2, 3], [4, 5], [7, 8, 9]]

test "PrefixSums.block" :=
  (PrefixSums.of PrefixSums.example).block 0 3 0 3 == 39
    ∧ (PrefixSums.of PrefixSums.example).block 1 3 1 3 == 22
    ∧ (PrefixSums.of PrefixSums.example).block 1 2 2 3 == 0
    ∧ (PrefixSums.of PrefixSums.example).block 2 2 0 3 == 0
test "PrefixSums.blockSpec" := PrefixSums.blockSpec PrefixSums.example 1 3 1 3 == 22
test "PrefixSums.table" := PrefixSums.table [0, 0] [[0, 1], [0, 2]] == [[0, 0], [0, 1], [0, 3]]
test "PrefixSums of no rows" := (PrefixSums.of []).block 0 0 0 0 == 0
