-- A `let` performs nothing unless its value or the rest of the block does
-- (docs/proposals/let.md, stage 1). A pure block is an ordinary term, not a
-- computation run by `Effect.runPure`, so a `let` can hold a proof, and a
-- function with a `let` unfolds to what it would without one.

import Std (IO, Nat)

-- A `let` holding a proof.
theorem two (n: Nat): n <= Succ (Succ n) :=
  let h := Nat.leSucc n
  Nat.leTrans n (Succ n) (Succ (Succ n)) h (Nat.leSucc (Succ n))

-- Two in a row, the second using the first.
theorem three (n: Nat): n <= Succ (Succ (Succ n)) :=
  let h1 := Nat.leSucc n
  let h2 := Nat.leTrans n (Succ n) (Succ (Succ n)) h1 (Nat.leSucc (Succ n))
  Nat.leTrans n (Succ (Succ n)) (Succ (Succ (Succ n))) h2 (Nat.leSucc (Succ (Succ n)))

-- An `if` after a `let` unfolds to the same term as without the `let`
-- (no `runPure`, no `Done` in either branch).
def withLet (n: Nat): Nat :=
  let m := n + 1
  if m < 3 then 0 else m

def withoutLet (n: Nat): Nat := if n + 1 < 3 then 0 else n + 1

theorem sameShape (n: Nat): withLet (n + 5) = withoutLet (n + 5) := rfl

-- The value is computed once at run time, and the function unfolds to the
-- body with the value substituted.
def twice (n: Nat): Nat :=
  let m := n + 1
  m + m

theorem twiceUnfolds (n: Nat): twice n = (n + 1) + (n + 1) := rfl

-- Binding a function that performs an ability is pure: only calling it
-- performs.
ability Ask where
  ask: () -> {Ask} Nat

def bindsEffectful (n: Nat): Nat :=
  let f: () -> {Ask} Nat := u => ask() + n
  n + 1

theorem bindsEffectfulPure (n: Nat): bindsEffectful n = n + 1 := rfl

-- Calling a function bound by a `let` performs what its type says.
def callsBound (n: Nat): {Ask} Nat :=
  let f: () -> {Ask} Nat := u => ask() + n
  let k := n * 2
  f() + k

def answer (n: Nat): Nat :=
  handle callsBound n with
    | return x => x
    | ask u, k => k 10

test "callsBound" := answer 3 == 19

-- Handling inside a pure block: the `let` is pure, the rest handles what
-- it performs.
def handled (n: Nat): Nat :=
  let f: () -> {Ask} Nat := u => ask() + n
  handle f() with
    | return x => x
    | ask u, k => k 1

test "handled" := handled 4 == 5

-- Dot notation after an effectful `let`: the variable's type as written is
-- the final (pure) call's result type, `Grid`, so `grid.rolls` finds
-- `Grid.rolls`.
def Grid: Type := List (List Nat)

def Grid.parse (lines: List Text): Grid := lines.map (l => [l.length])

def Grid.rolls (grid: Grid): Nat := grid.length

def countRolls(): {IO} () :=
  let grid := Grid.parse IO.readAllLines()
  IO.print grid.rolls.toText
