-- SW-963 (2), AoC 2021 day 10: a lambda argument checked before a later
-- argument fixes a `_` its hypothesis mentions (`lambdaFirst`), and `rfl`
-- checked before the expected type fixes a `_` (`rflUnderHole`).
import Std (Eq, List, Nat, Option, Void)

def next (n: Nat): Option Nat := Some (n + 1)

-- Day 10's `traverseMap _ g h (each) xs ys hyp`, cut down: `f` is a `_`
-- fixed only by `ran`, after the lambda, whose `rewrite` and `omega` need
-- `f x`'s value.
theorem eachStep ∀ (f: Nat → Option Nat) (each: (x: Nat) → (y: Nat) → f x = Some y → x < y) (xs: List Nat) (ran: List.map xs f = List.map xs next) (x: Nat) (y: Nat) (h: f x = Some y): x < y :=
  each x y h

-- With nothing expected of the call (a `let`), the lambda is checked where
-- it stands, and its `omega` meets `?f a`. (As a theorem's body, the same
-- call checks today: the lambda fails in place and is checked again after
-- the application's end, the after-expected path.)
def lambdaFirst (xs: List Nat) (x: Nat) (y: Nat) (h: next x = Some y): Nat :=
  let fact := eachStep _ (a b found => rewrite <- Option.someInjective _ _ found in omega) xs rfl x y h
  0

-- Day 10's `firstIllegalOfScan _ Curly rfl`: the `_` is fixed only by the
-- expected type, on which the result type depends. `rfl` fails in place
-- and is checked again after the expected type, but against its goal as
-- computed before the `_` was solved, so `firstOf [3, 4]` stays stuck
-- (with the goal evaluated afresh it checks).
def firstOf (xs: List Nat): Option Nat := List.head xs

type Starts: List Nat → Nat → Prop =
  | Here (n: Nat) (rest: List Nat): Starts (Cons n rest) n

theorem startsOf: (xs: List Nat) → (n: Nat) → firstOf xs = Some n → Starts xs n
  | Nil, n, h => Void.exfalso (Option.noneNotSome n h)
  | Cons m rest, n, h => rewrite <- Option.someInjective m n h in Here m rest

theorem rflUnderHole: Starts [3, 4] 3 := startsOf _ 3 rfl
