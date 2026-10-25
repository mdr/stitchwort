-- `List.filter` with a partial predicate: like `List.map`, its callback's
-- row is `{e}`, so the filter is partial too and the caller says `Partial`
-- (docs/proposals/effect-polymorphic-list.md, D1239). A pure predicate keeps
-- it the plain filter.
import Std (List, Nat)

def collatzSteps (n: Nat): {Partial} Nat :=
  if n ≤ 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

def isQuick (n: Nat): {Partial} Bool := Nat.leq (collatzSteps n) 9

def quickOnes (numbers: List Nat): {Partial} (List Nat) := List.filter numbers isQuick

def evens (numbers: List Nat): List Nat := List.filter numbers (n => n % 2 == 0)

test "filter with a partial predicate" := quickOnes [3, 7, 27, 8] == [3, 8]
test "filter with a pure one" := evens [3, 4, 8] == [4, 8]
