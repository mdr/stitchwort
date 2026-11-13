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
theorem autoFirst (c: Char) (first: Char) (tail: List Char) (positive: 0 < List.count [first, ..tail] (== c)):
    c ∈ [first, ..tail] :=
  List.memOfCountPositive c [first, ..tail] (omega [positive])

-- Only the call's own instances are found before its searches: here the
-- `+` of the lambda of the call around it (`x => x + 5`) is left until
-- that call has resumed its waiting `5`. Found early, the outer call's
-- type would compute through it to a value stuck on the `5`'s
-- placeholder, which isn't computed again once the `5` is filled
-- (`std/Float/Theory.sw`'s `unitsRoundNonpos` has this shape).
def capped (m: Nat): Nat := if m < 100 then m + 0 else m

theorem cappedExact (m: Nat) (pm: 0 < m) (hm: m < 100): capped m = m := match c: m < 100 with
  | True => rfl
  | False => rfl

theorem cappedSelf (x: Nat) (p: 0 < x): capped x + 5 = capped x + 5 := rfl

theorem outerLambda (k: Nat) (hm: Succ k < 100): capped (Succ k) + 5 = Succ k + 5 :=
  Eq.trans (cappedSelf (Succ k) (omega)) (Eq.cong (x => x + 5) (cappedExact (Succ k) (omega) hm))
