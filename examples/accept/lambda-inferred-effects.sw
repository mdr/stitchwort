-- A lambda with no type written may perform abilities: its body works out
-- the row of its result, which is the abilities it performs, as if written.

import Std (Fail, List, Result, Text)

ability Counter where
  next: () → {Counter} Nat

ability Ask where
  ask: () → {Ask} Nat

ability Log where
  log: (n: Nat) → {Log} ()

-- Answers `next` with 1, 2, 3, …
def counting (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => current => resume (current + 1) (current + 1)
  run 0

-- Answers `ask` with `answer`.
def asking (answer: Nat) (prog: () → {Ask | e} a): {e} a :=
  handle prog() with
    | return result => result
    | ask (), resume => resume answer

-- Keeps what `log` is given, in order.
def logging (prog: () → {Log | e} a): {e} (a, List Nat) :=
  handle prog() with
    | return result => (result, [])
    | log n, resume =>
      let (result, logged) := resume ()
      (result, Cons n logged)

-- One ability, called twice: each call performs it.
def twoDraws (): {Counter} Nat :=
  let later := () => next() * 10
  later () + later ()

test "one ability, called twice" := counting twoDraws == 30

-- Two abilities in one body: the row is both.
def drawAndAsk (): {Counter, Ask} Nat :=
  let later := () => next() + ask()
  later () + later ()

test "two abilities" := (counting (() => asking 100 drawAndAsk)) == 203

-- Two abilities, one after the other, with a parameter typed by its use.
def logThenDraw (): {Log, Counter} Nat :=
  let later := n =>
    log n
    next() + n
  later 3 + later 4

test "in sequence" := (counting (() => logging logThenDraw)) == (10, [3, 4])

-- With the parameter's type written.
def typedParameter (): {Log, Counter} Nat :=
  let later := (n: Nat) =>
    log n
    next() + n
  later 3

test "typed parameter" := (counting (() => logging typedParameter)) == (4, [3])

-- Fail, then Ask.
def failOrAsk (limit: Nat): {Fail, Ask} Nat :=
  let checked := () =>
    let n := ask()
    Fail.ensure (n < limit) "too big"
    n
  checked ()

test "Fail and Ask" :=
  asking 5 (() => Fail.toResult (() => failOrAsk 10)) == Ok 5
    ∧ asking 50 (() => Fail.toResult (() => failOrAsk 10)) == Err "too big"

-- Calling a function-valued parameter, and another such lambda.
def callsParameter (f: () → {Ask} Nat): {Ask} Nat :=
  let viaParameter := () => f () + 1
  let viaOther := () => viaParameter () + 2
  viaOther ()

test "calls a parameter" := asking 7 (() => callsParameter (() => ask() * 2)) == 17

-- Passed on to an effect-polymorphic function.
def drawEach (xs: List Nat): {Counter} List Nat :=
  let draw := x => next() + x
  xs.map draw

test "passed on" := counting (() => drawEach [10, 20, 30]) == [11, 22, 33]

-- Bound and never called: binding performs nothing.
def neverCalled (): Nat :=
  let later := () => next()
  3

test "never called" := neverCalled () == 3
