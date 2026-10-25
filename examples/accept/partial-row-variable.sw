-- Handlers whose rows have abilities and a row variable, `{A | e}`, take
-- partial programs with no change to their source
-- (docs/proposals/partial-handlers.md §4, D1255). Their result is partial
-- only when the program is: around total code they compute as before, and
-- the proofs about them still hold.

import Std (Each, Fail, IO, Pair)

-- Echoes every line it reads, until the input runs out: a loop with no
-- bound, so it's partial.
def echo(): {IO, Partial} () :=
  match IO.readLine() with
    | None => ()
    | Some line =>
      IO.print line
      echo()

-- `IO.simulate` around it: partial too, and a test can run it, since a
-- scripted input runs out.
def echoed (lines: List Text): {Partial} List Text := Pair.fst (IO.simulate lines echo)

test "a simulated loop" := echoed ["a", "b", "c"] == ["a", "b", "c"]
test "no input, no output" := echoed [] == []

-- Fails at 3, on its way down.
def countdown (n: Nat): {Fail, Partial} Nat :=
  if n == 3 then Fail.fail "three" else if n == 0 then 0 else countdown (n - 1)

-- `Fail.toResult` around a partial loop: partial.
def caught (n: Nat): {Partial} Result Nat Text := Fail.toResult (() => countdown n)

test "a failure is caught" := caught 5 == Err "three"
test "no failure" := caught 2 == Ok 0

-- `Each.collectIn` around partial code: each choice runs to its end, the
-- first before the second.
def collatzSteps: Nat → {Partial} Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def stepsOfEach (xs: List Nat): {Partial} List Nat := Each.collectIn (() => collatzSteps (Each.each xs))

test "every choice" := stepsOfEach [6, 7, 27] == [8, 16, 111]

-- Around total code, the same handlers are total, and compute: so a proof
-- by `rfl` about them holds.
def parsed (t: Text): Result Nat Text := Fail.toResult (() => t.toNatOrFail)

theorem parsedSeven: parsed "7" = Ok 7 := rfl

def echoedOnce: Pair (List Text) () :=
  IO.simulate ["hi"] (() =>
    match IO.readLine() with
      | None => ()
      | Some line => IO.print line)

theorem echoedOnceHi: echoedOnce = MkPair ["hi"] () := rfl

theorem collectedTotal: Each.collectIn (() => Each.each [1, 2, 3] + 1) = [2, 3, 4] := rfl
