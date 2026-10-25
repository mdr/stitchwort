-- State-passing handlers, which the backends run as a loop with the state in
-- a variable (docs/proposals/effect-runtime.md §9.1.5, stage 4d): a clause
-- that ends with `k v s′` jumps, and every other use of `k` (not in tail
-- position, twice, many times, stored and resumed after the handler has
-- returned) gets a real resumption. Every case is checked against the
-- reference evaluator, whose computations are trees.
--
-- run: tallied []
-- run: tallied [0, 0, 0]
-- run: tallied [0, 1, 0]
-- run: tallied [0, 2, 0]
-- run: tallied [2, 2, 0]
-- run: tallied [3, 0, 3]
-- run: tallied [4, 4, 4, 4, 4, 0]
-- run: tallied [5, 5, 0, 5]
-- run: tallied [0, 2, 3, 4, 5, 1, 0]
-- run: talliedOpen [0, 2, 3, 4, 5, 1, 0]
-- run: talliedOpen [2, 2, 3, 0]
-- run: talliedChecked [0, 2, 3, 4, 5, 1, 0]
-- run: talliedChecked [2, 2, 3, 0]
-- run: stored 3
-- run: stored 0
-- run: nestedState [1, 2, 3]
-- run: stateInState [1, 2, 3]
-- run: stores [4, 0, 7, 9]
-- run: storesEta [4, 0, 7, 9]
-- run: storesEtaOpen [4, 0, 7, 9]

import Std (Fail, List, Nat, Result, Text)

-- Each operation resumes a different number of times: `tick` once, in tail
-- position (a jump); `stop` never; `both` twice, not in tail position;
-- `many n` `n` times, under a lambda; `branch` once in either branch of an
-- `if`; `mixed` once, in tail position in one branch and not in the other.
ability Tally where
  tick: () → {Tally} Nat
  stop: () → {Tally} Nat
  both: () → {Tally} Nat
  many: Nat → {Tally} Nat
  branch: () → {Tally} Nat
  mixed: () → {Tally} Nat

def resumeAll (k: Nat → Nat → {e} List Nat) (s: Nat): Nat → {e} List Nat
  | 0 => []
  | Succ n => resumeAll k s n ++ k n (s + n)

-- At the closed empty row: the clauses' results are `Done` of the state's
-- function.
def Tally.run (prog: () → {Tally} List Nat): Nat → List Nat :=
  handle prog() with
    | return x => s => x ++ [s]
    | Tally.tick u, k => s => k s (s + 1)
    | Tally.stop u, k => s => [s]
    | Tally.both u, k => s => k s (s + 1) ++ k (s * 10) s
    | Tally.many n, k => s => resumeAll (i => t => k i t) s n
    | Tally.branch u, k => s => if s < 3 then k s (s + 1) else k 100 0
    | Tally.mixed u, k => s => if s == 0 then [7] ++ k 0 1 else k s (s - 1)

-- The same, written for an open row: at the empty row it's the empty-row
-- variant that runs, with the clauses' results the state's functions
-- themselves; with an ability outside, it isn't a state-passing handler at
-- the empty row, and resumes lazily.
def Tally.runIn (init: Nat) (prog: () → {Tally | e} List Nat): {e} List Nat :=
  let run: Nat → {e} List Nat :=
    handle prog() with
      | return x => s => x ++ [s]
      | Tally.tick u, k => s => k s (s + 1)
      | Tally.stop u, k => s => [s]
      | Tally.both u, k => s => k s (s + 1) ++ k (s * 10) s
      | Tally.many n, k => s => resumeAll (i => t => k i t) s n
      | Tally.branch u, k => s => if s < 3 then k s (s + 1) else k 100 0
      | Tally.mixed u, k => s => if s == 0 then [7] ++ k 0 1 else k s (s - 1)
  run init

-- Performs one operation for each code, at most eight, and lists what
-- each gave.
def drive (codes: List Nat): {Tally} List Nat :=
  List.map (List.take codes 8) (code =>
    if code == 0 then Tally.tick()
    else if code == 1 then Tally.stop()
    else if code == 2 then Tally.both()
    else if code == 3 then Tally.many 3
    else if code == 4 then Tally.branch()
    else Tally.mixed())

export def tallied (codes: List Nat): List Nat :=
  Tally.run (() => drive codes) 0

export def talliedOpen (codes: List Nat): List Nat :=
  Tally.runIn 0 (() => drive codes)

export def talliedChecked (codes: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => Tally.runIn 0 (() => drive codes))

-- A generator with a counter: the resumption is stored in the result,
-- under a lambda, and resumed after the handler has returned, several
-- times, with different answers.
ability Offer where
  offer: Nat → {Offer} Nat

type Paused =
  | Finished (total: Nat)
  | Suspended (count: Nat) (resume: Nat → Paused)

def Offer.counted (prog: () → {Offer} Nat): Nat → Paused :=
  handle prog() with
    | return x => s => Finished (x * 100 + s)
    | Offer.offer v, k => s => Suspended s (answer => k (v + answer) (s + 1))

def offers (start: Nat): {Offer} Nat :=
  let a := Offer.offer start
  let b := Offer.offer (a + 1)
  a * 1000 + b

-- Answers 1, 2 and 1 again to every offer, to a depth of four.
def explore: Nat → Paused → List Nat
  | 0, p => []
  | Succ depth, Finished total => [total]
  | Succ depth, Suspended count resume =>
    [count] ++ explore depth (resume 1) ++ explore depth (resume 2) ++ explore depth (resume 1)

export def stored (start: Nat): List Nat :=
  explore 4 (Offer.counted (() => offers start) 5)

-- A state handler around a handler of another ability: the counter's
-- operations are forwarded through the reader's handler.
ability Counter where
  next: () → {Counter} Nat

def Counter.number (prog: () → {Counter} a): Nat → a :=
  handle prog() with
    | return x => s => x
    | Counter.next u, k => s => k s (s + 1)

ability Env where
  ask: () → {Env} Nat

def Env.give (value: Nat) (prog: () → {Env | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

export def nestedState (numbers: List Nat): List Nat :=
  Counter.number (() => Env.give 5 (() => List.map numbers (x => x * 10 + Counter.next() + Env.ask()))) 3

-- Two state handlers, one inside the other: the inner one is written for
-- an open row and used with `Counter` outside, so only the outer one is at
-- the empty row.
export def stateInState (numbers: List Nat): List Nat :=
  Counter.number (() => Tally.runIn 100 (() => List.map numbers (x => x * 10 + Counter.next() + Tally.tick()))) 0

-- A store whose `put` doesn't take the state's function apart: `k ()` is
-- already a function of the state (`s => k () s`, as the backends read it).
-- At the closed empty row that clause is a computation, not `Done` of a
-- function, so the handler isn't run as a loop there: the plain handler is
-- the fallback.
ability Store where
  get: () → {Store} Nat
  put: Nat → {Store} ()

def Store.run (prog: () → {Store} a): Nat → a :=
  handle prog() with
    | return x => s => x
    | get u, k => s => k s s
    | put v, k => s => k () v

def Store.keep (prog: () → {Store} a): Nat → a :=
  handle prog() with
    | return x => s => x
    | get u, k => s => k s s
    | put v, k => k ()

def Store.keepIn (init: Nat) (prog: () → {Store | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return x => s => x
      | get u, k => s => k s s
      | put v, k => k ()
  run init

def accumulate (numbers: List Nat): {Store} List Nat :=
  List.map numbers (x =>
    put (get() + x)
    get())

export def stores (numbers: List Nat): List Nat :=
  Store.run (() => accumulate numbers) 1

export def storesEta (numbers: List Nat): List Nat :=
  Store.keep (() => accumulate numbers) 1

export def storesEtaOpen (numbers: List Nat): List Nat :=
  Store.keepIn 1 (() => accumulate numbers)
