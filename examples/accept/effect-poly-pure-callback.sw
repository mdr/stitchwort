-- A pure function where an effect-polymorphic callback is expected
-- (SW-393): `List.mapIn` takes `a -> {e} b`, and a pure `a -> b` fits it
-- with `e` empty, so the call is pure. A named function, a constructor, a
-- partial application and a parameter all work, as a lambda does.
import Std (List, Fail)

def double (n: Nat): Nat := n + n

def doubled (numbers: List Nat): List Nat := List.mapIn double numbers

def successors (numbers: List Nat): List Nat := List.mapIn Succ numbers

def tails (lists: List (List Nat)): List (List Nat) := List.mapIn (List.drop 1) lists

def mapPure (step: Nat -> Nat) (numbers: List Nat): List Nat := List.mapIn step numbers

def mapEmptyRow (step: Nat -> {} Nat) (numbers: List Nat): List Nat := List.mapIn step numbers

-- In a computation that may fail, a pure callback performs nothing.
def doubledOrFail (numbers: List Nat): {Fail} (List Nat) :=
  let doubledNumbers := List.mapIn double numbers
  if doubledNumbers == [] then Fail.fail "no numbers" else doubledNumbers

test "mapIn with a named function" := doubled [1, 2, 3] == [2, 4, 6]

test "mapIn with a constructor" := successors [0, 4] == [1, 5]

test "mapIn with a partial application" := tails [[1, 2], [3], []] == [[2], [], []]

test "mapIn with a pure parameter" := mapPure (n => n * 10) [1, 2] == [10, 20]

test "mapIn with an empty-row parameter" := mapEmptyRow double [5] == [10]

test "mapIn with a pure callback in a failing computation" :=
  Fail.toResult (() => doubledOrFail [1, 2]) == Ok [2, 4]
