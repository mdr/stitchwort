-- A comparison section, `(<)`, `(> 3)` or `(.fst <= 2)`, where nothing
-- has fixed its result type yet is the `Bool` comparison (SW-930), as
-- `a < b` written where a `Bool` is expected is: a generic function such as
-- `zipWith` or `map` gives a list of `Bool`s, which `count` can count.
-- Where a proposition is expected (`List.All`), the section is one.
-- (docs/syntax.md, "Operator sections".)

import Std (List)

-- How many measurements are deeper than the one `gap` places before them
-- (Advent of Code 2021, day 1).
def increasesOver (gap: Nat) (depths: List Nat): Nat :=
  depths.zipWith (depths.drop gap) (<) |> .count (deeper => deeper)

test "a bare comparison, zipped" := increasesOver 1 [199, 200, 208, 210, 200, 207] == 4

def deepCount (depths: List Nat): Nat := depths.map (> 200) |> .count (deep => deep)

test "a section with an operand, mapped" := deepCount [199, 200, 208, 210] == 2

def smallFirsts (pairs: List (Pair Nat Nat)): Nat := pairs.map (.fst <= 2) |> .count (small => small)

test "a method section that compares" := smallFirsts [MkPair 1 9, MkPair 3 0, MkPair 2 2] == 2

-- Where a proposition is expected, the section is the proposition.
theorem allSmall ∀ (xs: List Nat) (h: List.All (< 5) xs): List.All (< 5) xs := h
