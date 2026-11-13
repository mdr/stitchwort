-- Arguments whose types a later argument or the expected type fixes, in
-- the shapes AoC 2021 met that checked before stage 7 (SW-988, the design
-- of stage 7 in docs/proposals/postponement.md): as a theorem's body,
-- where an argument that fails in place is checked again once the call's
-- type is compared with the goal. Each has a twin in
-- docs/proposals/postponement/stage7/ where nothing is expected of the
-- call; stage 7 made those of days 13, 14 and 10's `rfl` check
-- (searches-after-call.sw, rfl-after-call.sw). The lambda of day 10 and
-- the two below them (days 12 and 16) are still open there.
import Std (Bool, Char, Eq, List, Nat, Option)

-- A function, then the list that says its parameter's type, then `omega`
-- about both (day 14). Checked against a goal, `omega` fails in place and
-- is checked again once the application's type is compared with the goal.
theorem positiveSum (f: a → Nat) (xs: List a) (h: 0 < List.sumBy xs f): 0 < List.sumBy xs f := h

theorem lambdaThenList (counts: List ((Char, Char), Nat)) (pair: (Char, Char)) (given: 0 < List.sumBy counts (entry => entry.snd * Bool.toNat (entry.fst == pair))):
    0 < List.sumBy counts (entry => entry.snd * Bool.toNat (entry.fst == pair)) :=
  positiveSum (entry => entry.snd * Bool.toNat (entry.fst == pair)) counts (omega [given])

-- A lambda whose hypothesis mentions a `_` a later argument fixes (day 10).
def next (n: Nat): Option Nat := Some (n + 1)

theorem eachStep (f: Nat → Option Nat) (each: ∀ (x y: Nat) => f x = Some y → x < y) (xs: List Nat) (ran: List.map xs f = List.map xs next) (x: Nat) (y: Nat) (h: f x = Some y): x < y :=
  each x y h

theorem lambdaBeforeHole (xs: List Nat) (x: Nat) (y: Nat) (h: next x = Some y): x < y :=
  eachStep _ (a b found => rewrite <- Option.someInjective found in omega) xs rfl x y h

-- A congruence lemma's functions, `_`, found from the goal (day 12).
def count (n: Nat): Nat := match n with
  | Zero => 1
  | Succ k => count k + 1

def listing (n: Nat): List Nat := match n with
  | Zero => [0]
  | Succ k => [n, ..listing k]

theorem countIsLength: ∀ (n: Nat) => count n = List.length (listing n)
  | Zero => rfl
  | Succ k => rewrite countIsLength k in rfl

theorem sums (xs: List Nat): List.sumBy xs count = List.sumBy xs (n => List.length (listing n)) :=
  List.sumByCong xs _ _ (n => match n with
    | Zero => rfl
    | Succ k => countIsLength (Succ k))

-- A predicate `_` the goal fixes, over a list that doesn't compute (2024
-- day 16).
def lookup (n: Nat): Option Nat := if n < 3 then Some n else None

theorem anyHole (xs: List Nat) (x: Nat) (member: x ∈ xs) (found: lookup x = Some 2): List.Any (y => lookup y = Some 2) xs :=
  List.anyIntro _ x xs member found
