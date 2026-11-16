-- A rule set may have the name of a function that dot notation reaches on
-- a value (`length` beside `List.length`). In `xs.length`, `.length` is
-- that function, not the set, so a definition that uses it can have a
-- lemma about it in the set `length`: the set doesn't become a part of the
-- definition's own cycle (`E-MUTUAL-SIGNATURE`). (docs/syntax.md,
-- "rewrite repeatedly".)
namespace Demo

import Std (Eq, List, Nat)

def total (lists: List (List Nat)): List Nat := lists.map (xs => xs.length)

theorem totalNil: total [] = [] := byComputing

theorem totalCons ∀ (xs: List Nat) (rest: List (List Nat)): total [xs, ..rest] = [xs.length, ..total rest] :=
  byComputing

rules length := [totalCons, totalNil]

theorem totalOne ∀ (xs: List Nat): total [xs] = [xs.length] := rewrite repeatedly [length]
