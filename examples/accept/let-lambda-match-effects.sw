-- A lambda bound by `let` with no written type, whose body is a `match`
-- whose arms perform abilities. Its result type is unknown while the body
-- is checked, and is the same for every arm, as a `match` with no expected
-- type has (docs/proposals/syntax-conveniences.md §4.4): splitting `k`
-- doesn't change it (SW-869).

import Std (Option)

ability Counter where
  next: () → {Counter} Nat

-- Answers `next` with 1, 2, 3, …
def counting (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => current => resume (current + 1) (current + 1)
  run 0

-- On a variable from outside the lambda, a `Nat`.
def outer (g: Nat → {e} Nat) (k: Nat): {e} Nat :=
  let h :=
    (x: Nat) =>
      match k with
        | 0 => g x
        | n => g n
  h 1

-- On one that's an `Option`.
def outerOption (g: Nat → {e} Nat) (k: Option Nat): {e} Nat :=
  let h :=
    (x: Nat) =>
      match k with
        | Some m => g (m + x)
        | None => g x
  h 1

-- On the lambda's own parameter.
def own (g: Nat → {e} Nat) (k: Nat): {e} Nat :=
  let h :=
    (x: Nat) =>
      match x with
        | 0 => g k
        | n => g n
  h 0

-- With a concrete ability.
def counted (k: Nat): {Counter} Nat :=
  let h :=
    (x: Nat) =>
      match k with
        | 0 => next() + x
        | n => next() + n
  h 10 + h 20

test "pure callback" := outer (x => x * 2) 0 == 2 ∧ outer (x => x * 2) 5 == 10

test "Option" := outerOption (x => x * 2) (Some 3) == 8 ∧ outerOption (x => x * 2) None == 2

test "own parameter" := own (x => x + 1) 4 == 5

test "Counter" := counting (() => counted 0) == 33 ∧ counting (() => counted 3) == 9
