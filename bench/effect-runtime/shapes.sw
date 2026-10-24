-- Handler shapes for the review of docs/proposals/effect-runtime.md
-- (docs/proposals/effect-runtime-review.md): handlers that the note's
-- benchmark (map.sw) doesn't exercise. Each export runs `List.mapIn` over the
-- list with one operation per element, under a different kind of handler.
-- Built and timed like map.sw:
--
--   stitchwort build --js bench/effect-runtime/shapes.sw -o OUT
--   node bench/effect-runtime/prototype.mjs OUT/shapes.js OUT/shapes-loop.js
--   node bench/effect-runtime/shapes.mjs OUT/shapes.js OUT/shapes-loop.js
--
-- or natively: printf 'asked\n100000\n' | stitchwort run bench/effect-runtime/shapes.sw

import Std (IO, Each, Fail, List, Option, Result, Text)

-- A reader: the clause resumes at once with a constant (tail-resumptive,
-- no parameter), and the handler's result is a plain value.
ability Env where
  ask: () -> {Env} Nat

def Env.give (value: Nat) (prog: () -> {Env} a): a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

export def asked (numbers: List Nat): List Nat :=
  Env.give 7 (() => List.mapIn (x => x + Env.ask()) numbers)

-- A writer that collects what is emitted: the clause uses the
-- continuation's result (not a tail call).
ability Emit where
  emit: Nat -> {Emit} ()

def Emit.collect (prog: () -> {Emit} a): List Nat :=
  handle prog() with
    | return x => []
    | Emit.emit v, k => Cons v (k ())

export def emitted (numbers: List Nat): List Nat :=
  Emit.collect (() => List.mapIn (x => Emit.emit x) numbers)

-- A reader inside a `Fail` handler: `ask` is forwarded through
-- `Fail.toResult` on its way out.
export def askedChecked (numbers: List Nat): Result (List Nat) Text :=
  Env.give 7 (() => Fail.toResult (() => List.mapIn (x => if x < 100000000 then x + Env.ask() else Fail.fail "big") numbers))

-- A search whose path is as long as the list: every element forks once and
-- one branch stops at once, so there is one result but `n` resumptions
-- nested inside one another (`Each.both` calls `k True` before `k False`).
export def searched (numbers: List Nat): List (List Nat) :=
  Each.collect (() => List.mapIn (x => Each.each [x]) numbers)

-- The same three handlers with an ability left over (`Fail`, handled
-- outside): the handler's result is then a computation, and its clauses are
-- effectful code, so a runtime may delay running `k`.
def Env.giveIn (value: Nat) (prog: () -> {Env | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

def Emit.collectIn (prog: () -> {Emit | e} a): {e} List Nat :=
  handle prog() with
    | return x => []
    | Emit.emit v, k => Cons v (k ())

export def askedIn (numbers: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => Env.giveIn 7 (() => List.mapIn (x => if x < 100000000 then x + Env.ask() else Fail.fail "big") numbers))

export def emittedIn (numbers: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => Emit.collectIn (() => List.mapIn (x => if x < 100000000 then Emit.emit x else Fail.fail "big") numbers))

export def searchedIn (numbers: List Nat): Result (List (List Nat)) Text :=
  Fail.toResult (() => Each.collectIn (() => List.mapIn (x => if x < 100000000 then Each.each [x] else Fail.fail "big") numbers))

def total (xs: List Nat): Nat := List.sum xs

def main(): {IO} () :=
  let variant := Option.getOrElse "" (IO.readLine())
  let size := Option.getOrElse 0 (Text.toNat (Option.getOrElse "0" (IO.readLine())))
  let numbers := List.range size
  let answer :=
    if variant == "asked" then total (asked numbers)
    else if variant == "emitted" then total (emitted numbers)
    else if variant == "askedChecked" then (match askedChecked numbers with
      | Ok xs => total xs
      | Err m => 0)
    else if variant == "searched" then List.length (searched numbers)
    else 0
  IO.print "${variant} ${size}: ${answer}"
