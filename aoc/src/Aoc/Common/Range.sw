-- Generic range code, shared between days. Its tests are in `Aoc.Common.Tests`
-- (Tests/); the proofs about it in `Aoc.Common.Proofs` (Proofs/).

namespace Aoc.Common
import Std (List, Text)

-- A range of ids, both ends included: "3-5" is `{ from = 3, to = 5 }`.
type Range = { from: Nat, to: Nat }

def Range.parse (t: Text): Option Range :=
  match (t.split '-').map Text.toNat with
    | [Some from, Some to] => Some { from, to }
    | _                    => None

def Range.contains (r: Range) (id: Nat): Bool := r.from <= id && id <= r.to

def Range.size (r: Range): Nat := r.to + 1 - r.from

def Range.ids (r: Range): List Nat := List.rangeFrom r.size r.from

