-- Benchmark for docs/proposals/effect-runtime.md: `List.mapIn` with an
-- effectful callback over a long list, against plain `List.map`. Run with
-- bench/effect-runtime/run.sh, or by hand:
--
--   printf 'state\n10000\n' | stitchwort run bench/effect-runtime/map.sw
--   printf 'state\n10000\n' | stitchwort run --js bench/effect-runtime/map.sw
--
-- The first input line names the variant, the second is the list's length.
-- Each variant prints the sum of the mapped list, so nothing is skipped.

import Std (IO, Each, Fail, List, Option, Result, Text)

-- A counter, handled by passing the next number along (a state handler).
ability Counter where
  next: () -> {Counter} Nat

def Counter.number (prog: () -> {Counter} a): Nat -> a :=
  handle prog() with
    | return x => (s => x)
    | Counter.next u, k => (s => k s (s + 1))

-- Pure `map`: the baseline.
export def plain (numbers: List Nat): List Nat := List.map (x => x + 1) numbers

-- `mapIn` with a pure callback (the empty row).
export def pureMapIn (numbers: List Nat): List Nat := List.mapIn (x => x + 1) numbers

-- `mapIn` with `State`-like effect: every element performs `next`.
export def counted (numbers: List Nat): List Nat :=
  Counter.number (() => List.mapIn (x => x + Counter.next()) numbers) 0

-- `mapIn` with `Fail`, never failing: every element is in `{Fail}`, but no
-- operation is performed.
export def checked (numbers: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => List.mapIn (x => if x < 100000000 then x + 1 else Fail.fail "too big") numbers)

-- `mapIn` with `Fail`, failing at the last element.
export def failsLast (limit: Nat) (numbers: List Nat): Result (List Nat) Text :=
  Fail.toResult (() => List.mapIn (x => if x + 1 < limit then x + 1 else Fail.fail "last") numbers)

-- Two handlers: `Fail` inside the counter, so each `next` passes through
-- `Fail.toResult` on its way out. Fails at `limit`.
export def countedChecked (limit: Nat) (numbers: List Nat): Result (List Nat) Text :=
  Counter.number (() => Fail.toResult (() => List.mapIn (x => if x < limit then x + Counter.next() else Fail.fail "limit") numbers)) 0

-- Many resumptions of one continuation: each element is `x` or `x + 10`, so
-- `n` elements give `2^n` lists. For checking that the runtime resumes a
-- continuation more than once correctly, not for timing.
export def choices (numbers: List Nat): List (List Nat) :=
  Each.collect (() => List.mapIn (x => Each.each [x, x + 10]) numbers)

-- `mapIn` with `IO`: every element is printed, so each is an operation that
-- `main`'s runner performs.
def echo (x: Nat): {IO} Nat :=
  IO.print "${x}"
  x

def total (result: Result (List Nat) Text): Nat :=
  match result with
    | Ok xs => List.sum xs
    | Err m => 0

def main(): {IO} () :=
  let variant := Option.getOrElse "" (IO.readLine())
  let size := Option.getOrElse 0 (Text.toNat (Option.getOrElse "0" (IO.readLine())))
  let numbers := List.range size
  let answer :=
    if variant == "plain" then List.sum (plain numbers)
    else if variant == "pure" then List.sum (pureMapIn numbers)
    else if variant == "state" then List.sum (counted numbers)
    else if variant == "fail" then total (checked numbers)
    else if variant == "failLast" then total (failsLast size numbers)
    else if variant == "io" then List.sum (List.mapIn echo numbers)
    else 0
  IO.print "${variant} ${size}: ${answer}"
