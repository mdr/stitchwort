-- Generic range code, shared between days. Its tests are in `Aoc.Common.Tests`
-- (Tests/); the proofs about it in `Aoc.Common.Proofs` (Proofs/).

namespace Aoc.Common
import Std (List, Parse)
import Std.Parse (char, nat, token)

-- A range of ids, both ends included: "3-5" is `{ from = 3, to = 5 }`.
type Range = { from: Nat, to: Nat }

-- "11-22" is `{ from = 11, to = 22 }`. Spaces around either number are
-- allowed: " 11 - 22 " reads the same. A range that ends before it starts
-- fails at its end.
def range(): {Parse} Range :=
  let from := token nat
  char '-'
  let to := token nat
  Parse.ensure (from ≤ to) "the range ${from}-${to} ends before it starts"
  { from, to }

def Range.contains (range: Range) (id: Nat): Bool := range.from ≤ id ∧ id ≤ range.to

def Range.size (range: Range): Nat := range.to + 1 - range.from

-- Every id in the range, one by one: only for small ranges and specs.
def Range.ids (range: Range): List Nat := List.rangeFrom range.size range.from
