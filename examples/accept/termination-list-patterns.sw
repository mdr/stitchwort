-- Overlapping list patterns, `[p]` before `[p, ..ps]`, with the recursive
-- call inside a `match`. After `[p]`, the last clause's `ps` is the tail
-- split again, `Cons head tail`, and the `match` is lifted into a function
-- of its own given `head` and `tail`. The rebuilt `Cons head tail` is still
-- the tail, so each call is on a smaller list. Pairs with the
-- soundness/termination-list-pattern-*.sw files.
import Std (Abort)

-- Pure, matching on a callback's result.
def firstSome: List (() → Option a) → Option a
  | [] => None
  | [p] => p()
  | [p, ..ps] =>
    match p() with
      | Some x => Some x
      | None => firstSome ps

-- Effectful: the scrutinee itself may abort.
def firstOk: List (() → {Abort} (Option a)) → {Abort} a
  | [] => Abort.abort()
  | [p] => Abort.need (p())
  | [p, ..ps] =>
    match p() with
      | Some x => x
      | None => firstOk ps

-- Effectful, the scrutinee handled.
def firstOkHandled: List (() → {Abort} a) → {Abort} a
  | [] => Abort.abort()
  | [p] => p()
  | [p, ..ps] =>
    match Abort.toOption p with
      | Some x => x
      | None => firstOkHandled ps

-- Two overlapping clauses before the general one: the tail is split twice.
def sumSmall: List Nat → Nat
  | [] => 0
  | [a] => a
  | [a, b] => a + b
  | [a, ..rest] =>
    match a < 5 with
      | True => a + sumSmall rest
      | False => sumSmall rest

-- A piece rebuilt from deeper fields: `Cons b rest` is the tail.
def risingSteps: List Nat → Nat
  | [] => 0
  | [a] => 0
  | [a, b, ..rest] =>
    match a < b with
      | True => 1 + risingSteps (Cons b rest)
      | False => risingSteps rest

-- A `let` first, then two nested `match`es.
def doubledSmall: List Nat → Nat
  | [] => 0
  | [a] => a
  | [a, ..rest] =>
    let doubled := a + a
    match doubled < 10 with
      | True =>
        match a == 0 with
          | True => doubledSmall rest
          | False => doubled + doubledSmall rest
      | False => doubled

-- The tail through a `let`, and two calls in one branch.
def whileSmall: List Nat → {Abort} Nat
  | [] => 0
  | [a] => a
  | [a, ..rest] =>
    let tail := rest
    match a < 3 with
      | True => whileSmall tail + whileSmall rest
      | False => Abort.abort()

test "firstSome" := firstSome [() => None, () => Some 2, () => Some 3] == Some 2
test "firstSome none" := firstSome [() => None, () => None] == (None: Option Nat)
test "firstOkHandled" := Abort.toOption (() => firstOkHandled [() => Abort.abort(), () => 4]) == Some 4
test "sumSmall" := sumSmall [1, 7, 2, 3] == 6
test "risingSteps" := risingSteps [1, 2, 3, 1] == 2
test "doubledSmall" := doubledSmall [0, 1, 2, 9] == 15
test "whileSmall" := Abort.toOption (() => whileSmall [1, 2]) == Some 4
