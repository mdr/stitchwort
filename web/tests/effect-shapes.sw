-- Effectful `List.map` over a long list, for the playground's tests of the
-- effect runtime (docs/proposals/effect-runtime.md §9.3, stage 4c; D1163):
-- crates/web's library tests and web/tests/browser.mjs run it with
-- 1,000,000 elements on the playground's limits. The first input line names
-- the shape, the second is the list's length; `ioRead` then reads a number
-- per element. Each shape prints the sum of its list (`io` prints every
-- element first).

import Std (Each, Fail, IO, List, Nat, Option, Result, Text)

-- A reader.
ability Env where
  ask: () -> {Env} Nat

def Env.give (value: Nat) (prog: () -> {Env} a): a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

def Env.giveIn (value: Nat) (prog: () -> {Env | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

-- A writer that collects what is emitted.
ability Emit where
  emit: Nat -> {Emit} ()

def Emit.collect (prog: () -> {Emit} a): List Nat :=
  handle prog() with
    | return x => []
    | Emit.emit v, k => Cons v (k ())

def Emit.collectIn (prog: () -> {Emit | e} a): {e} List Nat :=
  handle prog() with
    | return x => []
    | Emit.emit v, k => Cons v (k ())

-- A counter, as a state-passing handler.
ability Counter where
  next: () -> {Counter} Nat

def Counter.number (prog: () -> {Counter} a): Nat -> a :=
  handle prog() with
    | return x => (s => x)
    | Counter.next u, k => (s => k s (s + 1))

-- Every element printed: an `IO` operation per element, forwarded through
-- `Fail.toResult`.
def echo (x: Nat): {IO, Fail} Nat :=
  IO.print (Nat.toText x)
  if x < 100000000 then x else Fail.fail "too big"

-- A number read per element.
def readOne (x: Nat): {IO} Nat :=
  let line := IO.readLine()
  x + Option.getOrElse 0 (Text.toNat (Option.getOrElse "" line))

def sumOf (result: Result (List Nat) Text): Nat :=
  match result with
    | Ok xs => List.sum xs
    | Err message => 0

def sumOfAll (lists: List (List Nat)): Nat := List.sum (List.map List.sum lists)

def shape (name: Text) (numbers: List Nat): {IO} Nat :=
  let big := 100000000
  if name == "io" then sumOf (Fail.toResult (() => List.map echo numbers))
  else if name == "ioRead" then List.sum (List.map readOne numbers)
  else if name == "checked" then sumOf (Fail.toResult (() => List.map (x => if x < big then x + 1 else Fail.fail "big") numbers))
  else if name == "asked" then List.sum (Env.give 7 (() => List.map (x => x + Env.ask()) numbers))
  else if name == "askedChecked" then sumOf (Env.give 7 (() => Fail.toResult (() => List.map (x => if x < big then x + Env.ask() else Fail.fail "big") numbers)))
  else if name == "askedIn" then sumOf (Fail.toResult (() => Env.giveIn 7 (() => List.map (x => if x < big then x + Env.ask() else Fail.fail "big") numbers)))
  else if name == "emitted" then List.sum (Emit.collect (() => List.map (x => Emit.emit x) numbers))
  else if name == "emittedIn" then sumOf (Fail.toResult (() => Emit.collectIn (() => List.map (x => if x < big then Emit.emit x else Fail.fail "big") numbers)))
  else if name == "searched" then sumOfAll (Each.collect (() => List.map (x => Each.each [x]) numbers))
  else if name == "counted" then List.sum (Counter.number (() => List.map (x => x + Counter.next()) numbers) 0)
  else 0

def main(): {IO} () :=
  let name := Option.getOrElse "" (IO.readLine())
  let size := Option.getOrElse 0 (Text.toNat (Option.getOrElse "0" (IO.readLine())))
  IO.print "${name} ${size}: ${shape name (List.range size)}"
