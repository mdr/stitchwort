-- A lambda passed to an effectful list function (`map`, `filter`,
-- `foldLeft`) may `match` on a variable from outside it, here the
-- function's own parameter `k`, with arms that perform the callback's
-- abilities. Splitting on `k` doesn't change the lambda's row (SW-838).

import Std (List, Option)

ability Counter where
  next: () → {Counter} Nat

-- Answers `next` with 1, 2, 3, …
def counting (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => current => resume (current + 1) (current + 1)
  run 0

-- Effect-polymorphic, on an `Option`.
def gen (g: Nat → {e} Nat) (xs: List Nat) (k: Option Nat): {e} List Nat :=
  xs.map (x =>
    match k with
      | Some m => g (m + x)
      | None => g x)

test "pure callback" := gen (x => x * 2) [1, 2] (Some 5) == [12, 14]

test "pure callback, no offset" := gen (x => x * 2) [1, 2] None == [2, 4]

-- On a `Nat`, with a callback that performs an ability.
def offsets (g: Nat → {e} Nat) (xs: List Nat) (k: Nat): {e} List Nat :=
  xs.map (x =>
    match k with
      | 0 => g x
      | n => g (n + x))

def counted (x: Nat): {Counter} Nat := next() + x

test "callback performing Counter" :=
  counting (() => offsets counted [10, 20] 0) == [11, 22]
    ∧ counting (() => offsets counted [10, 20] 3) == [14, 25]

-- With a concrete ability, and in `filter` and `foldLeft`.
def keep (g: Nat → {Counter} Bool) (xs: List Nat) (k: Bool): {Counter} List Nat :=
  xs.filter (x =>
    match k with
      | True => g x
      | False => g 0)

def total (g: Nat → {e} Nat) (xs: List Nat) (k: Nat): {e} Nat :=
  xs.foldLeft 0 (acc x =>
    match k with
      | 0 => acc + g x
      | _ => acc)

-- Keeps the second element it sees.
def second (x: Nat): {Counter} Bool := next() == 2 && x > 0

test "filter" := counting (() => keep second [7, 8, 9] True) == [8]

test "foldLeft" := total (x => x + 1) [1, 2, 3] 0 == 9 ∧ total (x => x + 1) [1, 2, 3] 1 == 0
