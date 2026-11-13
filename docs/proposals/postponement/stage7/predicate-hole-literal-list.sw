-- SW-771 (item 2, AoC 2024 day 16) and SW-976 (3), AoC 2021 day 16: a `_`
-- that only the expected type fixes, where the expected type has already
-- been computed: `List.Any ?p [1, 2, 3, 4]` against the statement, which
-- reaches the call as the disjunction `lookup 1 = Some 2 ∨ …`, so `?p` is
-- met applied to numbers, and `found` is checked against `?p x`.
import Std (Eq, List, Nat, Option)

def lookup (n: Nat): Option Nat := if n < 3 then Some n else None

theorem anyHole ∀ (x: Nat) (member: x ∈ [1, 2, 3, 4]) (found: lookup x = Some 2): List.Any (y => lookup y = Some 2) [1, 2, 3, 4] :=
  List.anyIntro _ x [1, 2, 3, 4] member found

-- With a list that doesn't compute, it checks today.
theorem anyHoleVar ∀ (xs: List Nat) (x: Nat) (member: x ∈ xs) (found: lookup x = Some 2): List.Any (y => lookup y = Some 2) xs :=
  List.anyIntro _ x xs member found
