-- expect-error: E-EXPORT
-- A record crossing the JS boundary carries no proofs, so each proof field
-- needs a decision procedure to re-establish it from the data. There's none
-- for `Sorted`. examples/extract/records.sw exports a record whose proof
-- field has one.

import Std (List)

def Sorted (xs: List Nat): Prop := ∀ (n: Nat) => List.length xs ≤ n + List.length xs

type SortedList = { items: List Nat, sorted: Sorted items }

export def size (s: SortedList): Nat := List.length s.items
