-- A `_` for a record a function builds inline, in a proof that recurses
-- along with it. The argument after the `_` constrains only one of its
-- fields, so it can't fix the `_`; the call's expected type can, and the
-- argument is checked again once the call's type has been compared with it.

import Std (List)

type Tally = { seen: List Nat, total: Nat }

def count (tally: Tally): List Nat → Tally
  | [] => tally
  | [n, ..rest] => count { seen = tally.seen ++ [n], total = tally.total + n } rest

def Positive (n: Nat): Prop := n > 0

theorem countPositive ∀ (tally: Tally) (waiting: List Nat)
    (seen: List.All Positive tally.seen) (h: List.All Positive waiting): List.All Positive (count tally waiting).seen :=
  match waiting, h with
    | [], rest => seen
    | [n, ..waiting], Both positive rest =>
      countPositive _ waiting (List.allAppend Positive tally.seen [n] seen (Both positive Trivial)) rest

test "count" := (count { seen = [], total = 0 } [1, 2, 3]).total == 6
