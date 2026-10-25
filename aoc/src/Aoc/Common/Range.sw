-- Generic range code, shared between days. Its tests are in `Aoc.Common.Tests`
-- (Tests/); the proofs about it in `Aoc.Common.Proofs` (Proofs/).

namespace Aoc.Common
import Std (Fail, List, Text)
import Std.Fail (ensure, fail)

-- A range of ids, both ends included: "3-5" is `{ from = 3, to = 5 }`.
type Range = { from: Nat, to: Nat }

-- "11-22" is `{ from = 11, to = 22 }`. Spaces around either number are
-- allowed: " 11 - 22 " reads the same. Anything else fails, naming the text.
def Range.parse (text: Text): {Fail} Range :=
  match (text.split '-').map .trim.toNat with
    | [Some from, Some to] =>
      ensure (from ≤ to) "the range '${text}' ends before it starts"
      { from, to }
    | _ => fail "expected a range like 11-22, got '${text}'"

def Range.parseOption (text: Text): Option Range := Fail.toOption (() => Range.parse text)

def Range.contains (range: Range) (id: Nat): Bool := range.from ≤ id ∧ id ≤ range.to

def Range.size (range: Range): Nat := range.to + 1 - range.from

-- Every id in the range, one by one: only for small ranges and specs.
def Range.ids (range: Range): List Nat := List.rangeFrom range.size range.from
