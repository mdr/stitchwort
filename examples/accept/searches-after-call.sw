-- A proof search given as an argument (`omega`, `cases`, `ring`,
-- `rewrite`) is checked after the rest of its call: the other arguments,
-- the call's own waiting checks, its comparison with the expected type and
-- the instances now findable (stage 7, rule 1, in
-- docs/proposals/postponement.md). AoC 2021 met each shape below.
import Std (Bool, Char, DecEq, Eq, List, Nat)

-- Day 13 (SW-969): `cases` before the expected type fixed the `_`s solved
-- `?a.x = ?b.x` by making the second `_` the first.
type P = { x: Nat, y: Nat }

def shift (b: Bool) (p: P): P := if b then { p | x = p.x + 1 } else p

theorem holesExt (b: Bool) (p: P) (q: P) (sameX: q.x = (shift b p).x) (sameY: q.y = p.y): q = shift b p :=
  P.ext _ _ cases cases

-- Day 14 (SW-971): a lambda whose `.snd` and `==` wait for the list after
-- it, then `omega` about both, in a `match` scrutinee, where nothing is
-- expected of the call.
theorem positiveSum (f: a → Nat) (xs: List a) (h: 0 < List.sumBy xs f): 0 < List.sumBy xs f := h

def lambdaFirst (counts: List ((Char, Char), Nat)) (pair: (Char, Char)) (given: 0 < List.sumBy counts (entry => entry.snd * Bool.toNat (entry.fst == pair))): Nat :=
  match positiveSum (entry => entry.snd * Bool.toNat (entry.fst == pair)) counts (omega [given]) with
    | h => 0

-- Day 14: the `[auto eq: DecEq a]` dictionary of
-- `List.memOfCountPositive`, found once its type is known, before `omega`
-- reads its goal.
theorem autoFirst (c: Char) (first: Char) (tail: List Char) (positive: 0 < List.count (Cons first tail) (== c)):
    c ∈ Cons first tail :=
  List.memOfCountPositive c (Cons first tail) (omega [positive])
