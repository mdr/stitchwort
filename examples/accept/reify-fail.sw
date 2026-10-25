-- `match reify` (docs/proposals/proof-reification.md): in a proof, a split
-- on what a computation does first, with clauses written as a handler's.
-- In each clause the goal says what happened, so the handlers in it compute.

import Std (Abort, Fail, Option, Result, Text, Void)

-- The laws std proves this way, restated and proved again here.

theorem toResultThen (t: () -> {Fail} a) (k: a -> {Fail} b):
    Fail.toResult (() => k (t ())) = Result.flatMap (Fail.toResult t) (x => Fail.toResult (() => k x)) :=
  match reify t with
    | return x => rfl
    | Fail.stop msg, _ => rfl

theorem toOptionThen (t: () -> {Fail} a) (k: a -> {Fail} b):
    Fail.toOption (() => k (t ())) = Option.flatMap (Fail.toOption t) (x => Fail.toOption (() => k x)) :=
  match reify t with
    | return x => rfl
    | Fail.stop msg, _ => rfl

theorem toOptionToResult (t: () -> {Fail} a): Fail.toOption t = Result.toOption (Fail.toResult t) :=
  match reify t with
    | return x => rfl
    | Fail.stop msg, _ => rfl

theorem abortThen (t: () -> {Abort} a) (k: a -> {Abort} b):
    Abort.toOption (() => k (t ())) = Option.flatMap (Abort.toOption t) (x => Abort.toOption (() => k x)) :=
  match reify t with
    | return x => rfl
    | Abort.stop (), _ => rfl

-- A thunk written in place: the split is on `f x` itself.
theorem toResultMap (f: a -> {Fail} b): (xs: List a) ->
    Fail.toResult (() => xs.map f) = Result.traverse xs (x => Fail.toResult (() => f x))
  | [] => rfl
  | [x, ..xs] =>
    let rest := toResultMap f xs
    match reify (() => f x) with
      | return y =>
        match reify (() => xs.map f) with
          | return ys => rewrite <- rest in rfl
          | Fail.stop msg, _ => rewrite <- rest in rfl
      | Fail.stop msg, _ => rfl

-- Std's own, used.
theorem parsed (xs: List Text):
    Fail.toResult (() => xs.map Text.toNatOrFail) = Result.traverse xs (x => Fail.toResult (() => Text.toNatOrFail x)) :=
  Fail.toResultMap Text.toNatOrFail xs

-- A user's own ability, with two operations that resume: a one-step split
-- (R1 has no induction over the rest of the computation).

ability State (s: Type) where
  get: () -> {State s} s
  put: s -> {State s} ()

def runState (init: s) (prog: () -> {State s} a): Pair a s :=
  let run: s -> Pair a s :=
    handle prog() with
      | return x => st => MkPair x st
      | State.get u, k => st => k st st
      | State.put st2, k => st => k() st2
  run init

-- A predicate may use `reify` too: its type ends in `Prop`, so it's never
-- run. A computation is finished if it performs nothing more.
def Finished (t: () -> {State s} a): Prop :=
  match reify t with
    | return x => Unit
    | State.get (), _ => Void
    | State.put st, _ => Void

-- A finished computation leaves the state alone.
theorem finishedKeepsState (t: () -> {State s} a) (init: s) (finished: Finished t):
    Pair.snd (runState init t) = init :=
  match reify t with
    | return x => rfl
    | State.get (), _ => Void.exfalso finished
    | State.put st, _ => Void.exfalso finished

-- A computation that puts first.
def PutsFirst (t: () -> {State s} a): Prop :=
  match reify t with
    | return x => Void
    | State.get (), _ => Void
    | State.put st, _ => Unit

-- What it starts from doesn't matter: the `put` replaces it. In the `put`
-- clause, `rest` is the rest of the computation, from what `put` returns.
theorem putFirstForgets (t: () -> {State s} a) (init other: s) (first: PutsFirst t):
    runState init t = runState other t :=
  match reify t with
    | return x => Void.exfalso first
    | State.get (), _ => Void.exfalso first
    | State.put st, rest => rfl

-- A row of two abilities: a clause for each operation of each.
def FailsFirst (t: () -> {State Nat, Fail} a): Prop :=
  match reify t with
    | return x => Void
    | Fail.stop msg, _ => Unit
    | State.get (), _ => Void
    | State.put n, _ => Void

def ReadsFirst (t: () -> {State Nat, Fail} a): Prop :=
  match reify t with
    | return x => Void
    | Fail.stop msg, _ => Void
    | State.get (), _ => Unit
    | State.put n, _ => Void

-- Both facts about `t` are split with it.
theorem notBoth (t: () -> {State Nat, Fail} a) (fails: FailsFirst t) (reads: ReadsFirst t): Void :=
  match reify t with
    | return x => fails
    | Fail.stop msg, _ => reads
    | State.get (), rest => fails
    | State.put n, rest => fails
