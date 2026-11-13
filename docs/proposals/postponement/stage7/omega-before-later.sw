-- SW-971 (1), AoC 2021 day 14: an `omega` argument is checked before
-- what fixes its goal.
import Std (Bool, Char, DecEq, Eq, List, Nat)

-- A stand-in for day 14's `sumByPositive`: the function, then the list.
theorem positiveSum ∀ (f: a → Nat) (xs: List a) (h: 0 < List.sumBy xs f): 0 < List.sumBy xs f := h

-- The lambda's `.snd` and `==` wait for the list after it; `omega` runs on
-- a goal holding their placeholders. Day 14's call was a `match`
-- scrutinee, so nothing is expected of it and the after-expected path
-- doesn't run. (The same call as a theorem's body checks: `omega` fails in
-- place, and is checked again after the application's end.)
def lambdaFirst (counts: List ((Char, Char), Nat)) (pair: (Char, Char)) (given: 0 < List.sumBy counts (entry => entry.snd * Bool.toNat (entry.fst == pair))): Nat :=
  match positiveSum (entry => entry.snd * Bool.toNat (entry.fst == pair)) counts (omega [given]) with
    | h => 0

-- `List.memOfCountPositive [auto eq: DecEq a] (c: a): (xs: List a) → 0 < List.count xs (== c) → c ∈ xs`:
-- the dictionary is found only in the obligations loop, after the call, so
-- `omega`'s goal has `DecEq.%decide ?1 first c` where the fact has
-- `Char.decEq first c`, even when it is checked again after the expected
-- type.
theorem autoFirst ∀ (c: Char) (first: Char) (tail: List Char) (positive: 0 < List.count (Cons first tail) (== c)):
    c ∈ Cons first tail :=
  List.memOfCountPositive c (Cons first tail) (omega [positive])
