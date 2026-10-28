-- A rule left with holes whose left side needs an `auto` instance of a type
-- the holes leave unknown, as `List.sumByAdd xs _ _` needs `Add c` for
-- `List.sumBy xs (x => ?f x + ?g x)`: the occurrence's type fixes `c`, and
-- with it the instance, so the rule matches.
import Std (Eq, List, Nat)

theorem splitSum (xs: List Nat) (f: Nat → Nat) (g: Nat → Nat):
    List.sumBy xs (x => f x + g x) = List.sumBy xs f + List.sumBy xs g :=
  rewrite List.sumByAdd xs _ _ in rfl

-- Twice, splitting three summands.
theorem splitThree (xs: List Nat) (f: Nat → Nat) (g: Nat → Nat) (h: Nat → Nat):
    List.sumBy xs (x => f x + g x + h x) = List.sumBy xs f + List.sumBy xs g + List.sumBy xs h :=
  rewrite List.sumByAdd xs _ _, List.sumByAdd xs _ _ in rfl

-- Inside a function passed to `List.sumBy`, where the occurrence uses its
-- variable.
theorem splitInner (rows: List Nat) (cols: List Nat) (f: Nat → Nat → Nat) (g: Nat → Nat → Nat):
    List.sumBy rows (r => List.sumBy cols (c => f r c + g r c))
      = List.sumBy rows (r => List.sumBy cols (c => f r c)) + List.sumBy rows (r => List.sumBy cols (c => g r c)) :=
  rewrite List.sumByAdd cols _ _, List.sumByAdd rows _ _ in rfl
