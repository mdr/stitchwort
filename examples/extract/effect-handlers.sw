-- How resumptions behave in the effect runtime
-- (docs/proposals/effect-runtime.md §9.2): resumed any number of times,
-- stored in the handler's result and resumed after the handler has
-- returned, in different branches, and through nested handlers. Every case
-- is checked against the reference evaluator, whose computations are trees.
--
-- run: resumed []
-- run: resumed [0]
-- run: resumed [1]
-- run: resumed [2]
-- run: resumed [3, 2, 1]
-- run: resumed [2, 0, 3]
-- run: resumedChecked [3, 2, 1]
-- run: resumedChecked [2, 0, 3]
-- run: choices [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
-- run: choicesChecked [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
-- run: branches 4
-- run: branches 0
-- run: replayed 3 [5, 6]
-- run: nested 10 [1, 2, 3]
-- run: nested 100 [1, 2, 3]
-- run: translated 10 [1, 2, 3]
-- run: translated 100 [1, 2, 3]
-- run: stateThroughFail 5 [1, 2, 3, 4]
-- run: stateThroughFail 2 [1, 2, 3, 4]

import Std (Each, Fail, List, Nat, Result, Text)

-- `pick n` resumes `n` times, with 0 to n - 1: none, once, twice or many.
ability Pick where
  pick: Nat -> {Pick} Nat

def resumeEach (k: Nat -> {e} List Nat): Nat -> {e} List Nat
  | 0 => []
  | Succ n =>
    let before := resumeEach k n
    let after := k n
    List.append before after

def Pick.all (prog: () -> {Pick | e} Nat): {e} List Nat :=
  handle prog() with
    | return x => [x]
    | Pick.pick count, k => resumeEach k count

-- At most four picks, each of at most three, so at most 81 results.
def picks (counts: List Nat): {Pick} Nat :=
  List.sum (List.map (count => Pick.pick (Nat.min count 3) * 10) (List.take 4 counts))

-- At the empty row.
export def resumed (counts: List Nat): List Nat :=
  Pick.all (() => picks counts)

-- With `Fail` outside the handler, so resumption is lazy.
export def resumedChecked (counts: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => Pick.all (() => picks counts))

-- `Each`: every element forks into two, so ten elements give 1,024 lists.
export def choices (numbers: List Nat): List (List Nat) :=
  Each.collect (() => List.map (x => Each.each [x, x + 10]) (List.take 10 numbers))

export def choicesChecked (numbers: List Nat): Result (List (List Nat)) Text :=
  Fail.toResult (() => Each.collectIn (() => List.map (x => Each.each [x, x + 10]) (List.take 10 numbers)))

-- A generator: each `offer` suspends the program, and the handler's result
-- holds the resumption, which is called after the handler has returned. The
-- handler's row outside is closed and empty, so its fold's result is a
-- computation and the runtime resumes lazily.
ability Offer where
  offer: Nat -> {Offer} Nat

type Paused =
  | Finished (total: Nat)
  | Suspended (offered: Nat) (resume: Nat -> Paused)

def Offer.pause (prog: () -> {Offer} Nat): Paused :=
  handle prog() with
    | return x => Finished x
    | Offer.offer v, k => Suspended v (answer => k answer)

-- Offers its start and then each answer plus one, three times; the result
-- records every answer.
def threeOffers (start: Nat): {Offer} Nat :=
  let a := Offer.offer start
  let b := Offer.offer (a + 1)
  let c := Offer.offer (b + 1)
  a * 10000 + b * 100 + c

-- Answers every offer with the offered number plus `step`, for at most
-- `fuel` offers.
def settle: Nat -> Nat -> Paused -> Nat
  | 0, step, p => 0
  | Succ fuel, step, Finished total => total
  | Succ fuel, step, Suspended v resume => settle fuel step (resume (v + step))

def explore (p: Paused): List Nat :=
  match p with
    | Finished total => [total]
    | Suspended v resume =>
      -- The same resumption, resumed in three branches with different
      -- answers, one of them twice.
      [settle 5 1 (resume 1), settle 5 2 (resume 2), settle 5 1 (resume 1), settle 5 0 (resume 7)]

export def branches (start: Nat): List Nat :=
  explore (Offer.pause (() => threeOffers start))

-- Resumes the first stored resumption with each answer in turn, after the
-- handler is long gone, settling each run differently.
def replayFrom (p: Paused) (answers: List Nat): List Nat :=
  match p with
    | Finished total => [total]
    | Suspended v resume => List.map (answer => settle 5 answer (resume answer)) (List.take 5 answers)

export def replayed (start: Nat) (answers: List Nat): List Nat :=
  replayFrom (Offer.pause (() => threeOffers start)) answers

-- `depth` handlers nested (at most 100), each handling its own `Pick`-like
-- ability and forwarding the others: every operation of the innermost
-- program is forwarded outwards through all of them.
ability Env where
  ask: () -> {Env} Nat

def Env.give (value: Nat) (prog: () -> {Env} a): a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

ability Tick where
  tick: () -> {Tick} ()

-- Counts nothing, but each `tick` it handles resumes once.
def Tick.ignore (prog: () -> {Tick | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Tick.tick u, k => k ()

def layered: Nat -> (() -> {Env, Tick} a) -> {Env, Tick} a
  | 0, prog => prog()
  | Succ depth, prog => Tick.ignore (() => layered depth prog)

-- Each element asks the outermost handler and ticks to the innermost.
export def nested (depth: Nat) (numbers: List Nat): List Nat :=
  Env.give 7 (() => Tick.ignore (() => layered (Nat.min depth 100) (() => List.map (x =>
    Tick.tick()
    x + Env.ask()) numbers)))

-- A computation moved between rows `depth` times (at most 100), so each of
-- its operations is renamed by every `translate` on the way out and its
-- reply mapped back by each.
def widened: Nat -> (() -> {Env} a) -> {Env, Fail} a
  | 0, prog => prog()
  | Succ depth, prog =>
    match Fail.toResult (() => widened depth prog) with
      | Ok x => x
      | Err message => Fail.fail message

export def translated (depth: Nat) (numbers: List Nat): Result (List Nat) Text :=
  Env.give 3 (() => Fail.toResult (() => widened (Nat.min depth 100) (() => List.map (x => x * Env.ask()) numbers)))

-- A state handler outside a `Fail` handler: the counter's operations are
-- forwarded through `Fail.toResult`, which may stop the run part way.
ability Counter where
  next: () -> {Counter} Nat

def Counter.number (prog: () -> {Counter} a): Nat -> a :=
  handle prog() with
    | return x => (s => x)
    | Counter.next u, k => (s => k s (s + 1))

export def stateThroughFail (limit: Nat) (numbers: List Nat): Result (List Nat) Text :=
  Counter.number (() => Fail.toResult (() => List.map (x =>
    let n := Counter.next()
    if n < limit then x + n else Fail.fail "limit") numbers)) 0
