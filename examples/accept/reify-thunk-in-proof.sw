-- A law about thunks used on a thunk written where it's used: the thunk in
-- the proof is the same term as the one in the statement (SW-422). A thunk
-- `() => e` is a plain lambda, not a hidden function of its own.

import Std (Fail, Result, List)

theorem succThen (g: Nat -> {Fail} Nat) (n: Nat):
    Fail.toResult (() => Succ (g n)) = Result.flatMap (x => Fail.toResult (() => Succ x)) (Fail.toResult (() => g n)) :=
  Fail.toResultThen (() => g n) (x => Succ x)

theorem mapThen (f: Nat -> {Fail} Nat) (xs: List Nat) (k: List Nat -> {Fail} Nat):
    Fail.toResult (() => k (xs.mapIn f)) = Result.flatMap (ys => Fail.toResult (() => k ys)) (Fail.toResult (() => xs.mapIn f)) :=
  Fail.toResultThen (() => xs.mapIn f) k

theorem mapToOption (f: Nat -> {Fail} Nat) (xs: List Nat):
    Fail.toOption (() => xs.mapIn f) = Result.toOption (Fail.toResult (() => xs.mapIn f)) :=
  Fail.toOptionToResult (() => xs.mapIn f)

-- The same law by `rewrite`, in a longer goal.
theorem lengthThen (f: Nat -> {Fail} Nat) (xs: List Nat):
    Result.map List.length (Fail.toResult (() => Cons 0 (xs.mapIn f))) =
      Result.map List.length (Result.flatMap (ys => Ok (Cons 0 ys)) (Fail.toResult (() => xs.mapIn f))) :=
  rewrite Fail.toResultThen (() => xs.mapIn f) (ys => Cons 0 ys) in rfl

-- A thunk whose type mentions its `()` still splits it: the goal becomes
-- `P ()`.
def unitOnly: () -> Type
  | () => Nat

def thunkSplits: (u: ()) -> unitOnly u := () => 3
