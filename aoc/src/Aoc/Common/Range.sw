-- Generic range code, shared between days. Its tests are in `Aoc.Common.Tests`
-- (Tests/); the proofs about it in `Aoc.Common.Proofs` (Proofs/).

namespace Aoc.Common
import Std (Fail, List, Text)
import Std.Fail (ensure, fail)

-- A range of ids, both ends included: "3-5" is `{ from = 3, to = 5 }`.
type Range = { from: Nat, to: Nat }

-- "11-22" is `{ from = 11, to = 22 }`. Spaces around either number are
-- allowed: " 11 - 22 " reads the same. Anything else fails, naming the text.
def Range.read (t: Text): {Fail} Range :=
  match (t.split '-').map (part => part.trim.toNat) with
    | [Some from, Some to] =>
      ensure (from <= to) "the range '${t}' ends before it starts"
      { from, to }
    | _ => fail "expected a range like 11-22, got '${t}'"

def Range.parse (t: Text): Option Range := Fail.toOption (() => Range.read t)

def Range.contains (r: Range) (id: Nat): Bool := r.from <= id && id <= r.to

def Range.size (r: Range): Nat := r.to + 1 - r.from

-- Every id in the range, one by one: only for small ranges and specs.
def Range.ids (r: Range): List Nat := List.rangeFrom r.size r.from
