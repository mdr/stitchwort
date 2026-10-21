-- Generic range code, shared between days.

namespace Aoc.Common

-- A range of ids, both ends included: "3-5" is `{ from = 3, to = 5 }`.
type Range = { from: Nat, to: Nat }

def Range.parse (t: Text): Option Range :=
  match (t.split '-').map Text.toNat with
    | [Some from, Some to] => Some { from, to }
    | _                    => None

test "parse" := Range.parse "3-5" == Some { from = 3, to = 5 }
test "parse junk" := Range.parse "4-x" == None

def Range.contains (r: Range) (id: Nat): Bool := r.from <= id && id <= r.to

test "contains" := (Range.contains { from = 3, to = 5 } 3, Range.contains { from = 3, to = 5 } 5, Range.contains { from = 3, to = 5 } 6) == (True, True, False)

def Range.size (r: Range): Nat := r.to + 1 - r.from

test "size" := Range.size { from = 3, to = 5 } == 3

def Range.ids (r: Range): List Nat := List.rangeFrom r.size r.from

test "ids" := Range.ids { from = 3, to = 5 } == [3, 4, 5]
