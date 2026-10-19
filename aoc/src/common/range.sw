-- Code shared between days.

namespace Aoc.Common

-- A range of ids, both ends included: "3-5" is `{ lo = 3, hi = 5 }`.
type Range = { lo: Nat, hi: Nat }

def Range.parse (t: Text): Maybe Range :=
  match (t.split '-').map Text.toNat with
    | [Just lo, Just hi] => Just { lo, hi }
    | _                  => Nothing

test "parse" := Range.parse "3-5" == Just { lo = 3, hi = 5 }
test "parse junk" := Range.parse "4-x" == Nothing
