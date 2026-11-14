-- Handlers whose clauses only pass an operation on (`k (Pick.pick n)`),
-- which the runtime steps over (docs/proposals/operations-in-place.md,
-- stage B): between the program and the handler that answers, with state
-- in the outer handler, a resumption resumed many times and one stored and
-- resumed after its handler returned, a failure raised inside, and an
-- operation of another ability passing through. Every case is checked
-- against the reference evaluator, whose computations are trees.
--
-- run: counted 0 [1, 2, 3]
-- run: counted 3 [1, 2, 3]
-- run: counted 5 []
-- run: picked 0 [2, 3]
-- run: picked 2 [2, 3]
-- run: picked 4 [3, 1, 2]
-- run: stopped 3 [1, 2, 3]
-- run: stopped 3 [1, 7, 3]
-- run: stoppedPicks [2, 1]
-- run: stoppedPicks [3, 2]
-- run: branches 0 4
-- run: branches 3 4
-- run: mixed 2 [1, 2, 3]
-- run: tallied 0 [1, 2, 3]
-- run: tallied 4 [1, 2, 3]

import Std (Empty, List, Nat, Result, Text)

-- A counter whose state is the outer handler's.
ability Counter where
  next: () → {Counter} Nat

def Counter.number (prog: () → {Counter} a): Nat → a :=
  handle prog() with
    | return x => (s => x)
    | Counter.next u, k => (s => k s (s + 1))

-- Passes every `next` outwards and resumes with the answer.
def Counter.relay (prog: () → {Counter} a): {Counter} a :=
  handle prog() with
    | return x => x
    | Counter.next u, k => k Counter.next()

def Counter.relays: Nat → (() → {Counter} a) → {Counter} a
  | 0, prog => prog()
  | Succ depth, prog => Counter.relay (() => Counter.relays depth prog)

export def counted (depth: Nat) (numbers: List Nat): List Nat :=
  Counter.number (() => Counter.relays (Nat.min depth 20) (() => List.map numbers (x => x * 10 + Counter.next()))) 0

-- `pick n` resumes `n` times, with 0 to n - 1.
ability Pick where
  pick: Nat → {Pick} Nat

def resumeEach (k: Nat → {e} List Nat): Nat → {e} List Nat
  | 0 => []
  | Succ n =>
    let before := resumeEach k n
    let after := k n
    List.append before after

def Pick.all (prog: () → {Pick | e} Nat): {e} List Nat :=
  handle prog() with
    | return x => [x]
    | Pick.pick count, k => resumeEach k count

def Pick.relay (prog: () → {Pick | e} a): {Pick | e} a :=
  handle prog() with
    | return x => x
    | Pick.pick n, k => k (Pick.pick n)

def Pick.relays: Nat → (() → {Pick} a) → {Pick} a
  | 0, prog => prog()
  | Succ depth, prog => Pick.relay (() => Pick.relays depth prog)

-- At most three picks, each of at most three.
def picks (counts: List Nat): {Pick} Nat :=
  List.sum (List.map (List.take counts 3) (count => Pick.pick (Nat.min count 3) * 10))

export def picked (depth: Nat) (counts: List Nat): List Nat :=
  Pick.all (() => Pick.relays (Nat.min depth 20) (() => picks counts))

-- A failure: the outer handler never resumes, so the relays' resumptions
-- are dropped.
ability Stop where
  stop: Text → {Stop} Empty

def Stop.toResult (prog: () → {Stop | e} a): {e} Result a Text :=
  handle prog() with
    | return x => Ok x
    | Stop.stop message, k => Err message

def Stop.relay (prog: () → {Stop | e} a): {Stop | e} a :=
  handle prog() with
    | return x => x
    | Stop.stop message, k => k (Stop.stop message)

def Stop.relays: Nat → (() → {Stop} a) → {Stop} a
  | 0, prog => prog()
  | Succ depth, prog => Stop.relay (() => Stop.relays depth prog)

def checked (x: Nat): {Stop} Nat := if x > 5 then Empty.absurd (Stop.stop "too big: ${x}") else x + 1

export def stopped (depth: Nat) (numbers: List Nat): Result (List Nat) Text :=
  Stop.toResult (() => Stop.relays (Nat.min depth 20) (() => List.map numbers (x => checked x)))

-- Many resumptions, some of whose runs fail, through relays of both
-- abilities: `Pick`'s relay passes `stop` on by the generated forward.
def pickOrStop (counts: List Nat): {Pick, Stop} Nat :=
  let total := picks counts
  if total == 20 then Empty.absurd (Stop.stop "twenty") else total

export def stoppedPicks (counts: List Nat): List (Result Nat Text) :=
  Pick.all2 (() => Pick.relay (() => Stop.relay (() => pickOrStop counts)))

-- `Pick.all` for a program that may stop: each run's result.
def Pick.all2 (prog: () → {Pick, Stop} Nat): List (Result Nat Text) :=
  handle Stop.toResult (() => prog()) with
    | return x => [x]
    | Pick.pick count, k => resumeEachResult k count

def resumeEachResult (k: Nat → {e} List (Result Nat Text)): Nat → {e} List (Result Nat Text)
  | 0 => []
  | Succ n =>
    let before := resumeEachResult k n
    let after := k n
    List.append before after

-- A generator whose resumption is kept in the handler's result and resumed
-- after the handler has returned, in several branches.
ability Offer where
  offer: Nat → {Offer} Nat

type Paused = | Finished (total: Nat) | Suspended (offered: Nat) (resume: Nat → Paused)

def Offer.pause (prog: () → {Offer} Nat): Paused :=
  handle prog() with
    | return x => Finished x
    | Offer.offer v, k => Suspended v (answer => k answer)

def Offer.relay (prog: () → {Offer} a): {Offer} a :=
  handle prog() with
    | return x => x
    | Offer.offer v, k => k (Offer.offer v)

def Offer.relays: Nat → (() → {Offer} a) → {Offer} a
  | 0, prog => prog()
  | Succ depth, prog => Offer.relay (() => Offer.relays depth prog)

def threeOffers (start: Nat): {Offer} Nat :=
  let a := Offer.offer start
  let b := Offer.offer (a + 1)
  let c := Offer.offer (b + 1)
  a * 10000 + b * 100 + c

def settle: Nat → Nat → Paused → Nat
  | 0, step, p => 0
  | Succ fuel, step, Finished total => total
  | Succ fuel, step, Suspended v resume => settle fuel step (resume (v + step))

def explore (p: Paused): List Nat := match p with
  | Finished total => [total]
  | Suspended v resume => [settle 5 1 (resume 1), settle 5 2 (resume 2), settle 5 1 (resume 1)]

export def branches (depth start: Nat): List Nat :=
  explore (Offer.pause (() => Offer.relays (Nat.min depth 20) (() => threeOffers start)))

-- A relay of one ability while the program also counts, at a closed row:
-- the counter's operations pass the relays by their generated forwards.
def Pick.relayCounting (prog: () → {Pick, Counter} a): {Pick, Counter} a :=
  handle prog() with
    | return x => x
    | Pick.pick n, k => k (Pick.pick n)

def Pick.relaysCounting: Nat → (() → {Pick, Counter} a) → {Pick, Counter} a
  | 0, prog => prog()
  | Succ depth, prog => Pick.relayCounting (() => Pick.relaysCounting depth prog)

export def mixed (depth: Nat) (counts: List Nat): List Nat :=
  Counter.number (() => Pick.all (() => Pick.relaysCounting (Nat.min depth 20) (() => picks counts + Counter.next()))) 0

-- Only the counter's operations, each passing `depth` relays of `Pick` by
-- their generated forwards.
export def tallied (depth: Nat) (numbers: List Nat): List Nat :=
  Counter.number
    (() =>
      Pick.all (() =>
        Pick.relaysCounting (Nat.min depth 20) (() => List.sum (List.map numbers (x => x * Counter.next())))))
    0
