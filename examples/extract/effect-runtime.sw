-- Handler shapes over a long list, for the effect runtime
-- (docs/proposals/effect-runtime.md §9.3, stages 4a and 4d). Each export
-- maps a callback that performs an operation (or could) over the list, under a
-- different kind of handler. Checked here against the reference evaluator on
-- short lists; crates/cli/tests/effect_runtime.rs calls them with 1,000,000
-- elements on Node's default stack and counts the runtime's work.
--
-- run: checked [1, 2, 3]
-- run: failsLast 3 [0, 1, 2]
-- run: asked [1, 2, 3]
-- run: askedChecked [1, 2, 3]
-- run: askedIn [1, 2, 3]
-- run: emittedIn [1, 2, 3]
-- run: searchedIn [1, 2, 3]
-- run: countedIn [1, 2, 3]
-- run: emitted [1, 2, 3]
-- run: searched [1, 2, 3]
-- run: counted [1, 2, 3]
-- run: countedChecked 3 [1, 2, 3, 4]
-- run: countedChecked 9 [1, 2, 3, 4]
-- run: countedOpen [1, 2, 3]
-- run: logged [1, 2, 3]
-- run: forwarded 0 [1, 2]
-- run: forwarded 3 [1, 2]

import Std (Each, Fail, List, Nat, Result, Text)

-- A `Fail`-able callback that never fails: in `{Fail}`, performing nothing.
export def checked (numbers: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => List.map numbers (x => if x < 100000000 then x + 1 else Fail.fail "too big"))

-- Fails at the element equal to `limit - 1`.
export def failsLast (limit: Nat) (numbers: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => List.map numbers (x => if x + 1 < limit then x + 1 else Fail.fail "last"))

-- A reader: the clause resumes at once with a constant.
ability Env where
  ask: () → {Env} Nat

def Env.give (value: Nat) (prog: () → {Env} a): a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

def Env.giveIn (value: Nat) (prog: () → {Env | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

export def asked (numbers: List Nat): List Nat :=
  Env.give 7 (() => List.map numbers (x => x + Env.ask()))

-- The reader with a `Fail` handler inside it, which forwards `ask`.
export def askedChecked (numbers: List Nat): Result (List Nat) Text :=
  Env.give 7 (() => Fail.toResult (() => List.map numbers (x => if x < 100000000 then x + Env.ask() else Fail.fail "big")))

-- A writer that collects what is emitted: the clause uses the
-- continuation's result, not as a tail call.
ability Emit where
  emit: Nat → {Emit} ()

def Emit.collect (prog: () → {Emit} a): List Nat :=
  handle prog() with
    | return x => []
    | Emit.emit v, k => Cons v (k ())

def Emit.collectIn (prog: () → {Emit | e} a): {e} List Nat :=
  handle prog() with
    | return x => []
    | Emit.emit v, k => Cons v (k ())

-- A counter, as a state-passing handler.
ability Counter where
  next: () → {Counter} Nat

def Counter.number (prog: () → {Counter} a): Nat → a :=
  handle prog() with
    | return x => (s => x)
    | Counter.next u, k => (s => k s (s + 1))

def Counter.numberIn (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return x => s => x
      | Counter.next u, k => s => k s (s + 1)
  run 0

-- With an ability left over outside the handler (`Fail`, handled outside),
-- the handler's result is a computation and its clauses are effectful code:
-- the runtime resumes lazily, so none of these nests a call per operation.
export def askedIn (numbers: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => Env.giveIn 7 (() => List.map numbers (x => if x < 100000000 then x + Env.ask() else Fail.fail "big")))

export def emittedIn (numbers: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => Emit.collectIn (() => List.map numbers (x => if x < 100000000 then Emit.emit x else Fail.fail "big")))

-- A search with one long path: every element forks, and the second branch
-- stops at once.
export def searchedIn (numbers: List Nat): Result (List (List Nat)) Text :=
  Fail.toResult (() => Each.collectIn (() => List.map numbers (x => if x < 100000000 then Each.each [x] else Fail.fail "big")))

export def countedIn (numbers: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => Counter.numberIn (() => List.map numbers (x => if x < 100000000 then x + Counter.next() else Fail.fail "big")))

-- At the empty row, a clause that uses the continuation's result inside pure
-- code is a pure non-tail recursion, one level per operation: these keep
-- JS's stack limit (§9.1.7 of the note).
export def emitted (numbers: List Nat): List Nat :=
  Emit.collect (() => List.map numbers (x => Emit.emit x))

export def searched (numbers: List Nat): List (List Nat) :=
  Each.collect (() => List.map numbers (x => Each.each [x]))

-- State-passing handlers at the empty row: the backends run them as a loop
-- with the state in a variable (stage 4d, §9.1.5 of the note). `counted` is
-- at the closed empty row; `countedOpen` and `logged` use a handler written
-- for an open row at the empty row; `countedChecked` has a `Fail` handler
-- inside the counter.
export def counted (numbers: List Nat): List Nat :=
  Counter.number (() => List.map numbers (x => x + Counter.next())) 0

export def countedChecked (limit: Nat) (numbers: List Nat): Result (List Nat) Text :=
  Counter.number (() => Fail.toResult (() => List.map numbers (x => if x < limit then x + Counter.next() else Fail.fail "limit"))) 0

export def countedOpen (numbers: List Nat): List Nat :=
  Counter.numberIn (() => List.map numbers (x => x + Counter.next()))

-- A writer that keeps what is emitted in its state, in reverse.
def Emit.log (prog: () → {Emit | e} a): {e} List Nat :=
  let run: List Nat → {e} List Nat :=
    handle prog() with
      | return x => acc => List.reverse acc
      | Emit.emit v, k => acc => k () (Cons v acc)
  run []

export def logged (numbers: List Nat): List Nat :=
  Emit.log (() => List.map numbers (x => Emit.emit x))

-- `ask` forwarded through `depth` handlers of another ability (at most 100),
-- each with a `translate` into its row, on its way to the reader.
ability Tick where
  tick: () → {Tick} ()

def Tick.ignore (prog: () → {Tick | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Tick.tick u, k => k ()

def layered: Nat → (() → {Env} a) → {Env} a
  | 0, prog => prog()
  | Succ depth, prog => Tick.ignore (() => layered depth prog)

export def forwarded (depth: Nat) (numbers: List Nat): List Nat :=
  Env.give 7 (() => layered (Nat.min depth 100) (() => List.map numbers (x => x + Env.ask())))
