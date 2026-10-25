-- A law about thunks used on a thunk written where it's used: the thunk in
-- the proof is the same term as the one in the statement (SW-422). A thunk
-- `() => e` is a plain lambda, not a hidden function of its own.

import Std (Fail, Result, List)

theorem succThen (g: Nat -> {Fail} Nat) (n: Nat):
    Fail.toResult (() => Succ (g n)) = Result.flatMap (Fail.toResult (() => g n)) (x => Fail.toResult (() => Succ x)) :=
  Fail.toResultThen (() => g n) (x => Succ x)

theorem mapThen (f: Nat -> {Fail} Nat) (xs: List Nat) (k: List Nat -> {Fail} Nat):
    Fail.toResult (() => k (xs.map f)) = Result.flatMap (Fail.toResult (() => xs.map f)) (ys => Fail.toResult (() => k ys)) :=
  Fail.toResultThen (() => xs.map f) k

theorem mapToOption (f: Nat -> {Fail} Nat) (xs: List Nat):
    Fail.toOption (() => xs.map f) = Result.toOption (Fail.toResult (() => xs.map f)) :=
  Fail.toOptionToResult (() => xs.map f)

-- The same law by `rewrite`, in a longer goal.
theorem lengthThen (f: Nat -> {Fail} Nat) (xs: List Nat):
    Result.map (Fail.toResult (() => Cons 0 (xs.map f))) List.length =
      Result.map (Result.flatMap (Fail.toResult (() => xs.map f)) (ys => Ok (Cons 0 ys))) List.length :=
  rewrite Fail.toResultThen (() => xs.map f) (ys => Cons 0 ys) in rfl

-- A thunk whose type mentions its `()` still splits it: the goal becomes
-- `P ()`.
def unitOnly: () -> Type
  | () => Nat

def thunkSplits: (u: ()) -> unitOnly u := () => 3

-- The law on a thunk whose body is bigger than the call it makes: `t ()`
-- is moved into `toResult`'s row where it's written here, but inside the
-- law's `t` there. That row turns out empty, so neither move leaves a
-- trace and the two thunks are one term (SW-424).
theorem twiceThen (t: () -> {Fail} Nat):
    Fail.toResult (() => Succ (Succ (t ()))) = Result.flatMap (Fail.toResult (() => Succ (t ()))) (x => Ok (Succ x)) :=
  rewrite Fail.toResultThen (() => Succ (t ())) (x => Succ x) in rfl
