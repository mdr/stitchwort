-- Handlers used where a pure value is expected: nested in each other, in a
-- `map` callback, and around an effectful `map` (SW-438). A handler's result
-- is in a bare row (`Abort.toOption: (() -> {Abort | e} a) -> {e} Option a`),
-- so its call is elaborated as a plain call first, like any such function
-- (`check::pure_first`, docs/proposals/effect-polymorphism.md, stage 3).
import Std (Abort, Option, Fail, List, Result)

def half (n: Nat): {Abort} Nat := if n % 2 == 0 then n / 2 else Abort.abort()

def halfOrFail (n: Nat): {Fail} Nat := if n % 2 == 0 then n / 2 else Fail.fail "odd"

def halveTwice (first: () → {Abort} Nat): Option Nat :=
  Option.flatMap (Abort.toOption first) (x => Abort.toOption (() => half x))

test "nested handlers, both succeed" := halveTwice (() => half 8) == Some 2

test "nested handlers, the second stops" := halveTwice (() => half 6) == None

test "nested handlers, the first stops" := halveTwice (() => half 7) == None

def halveAll (numbers: List Nat): Option (List Nat) := Abort.toOption (() => numbers.map half)

test "a handler around map" := halveAll [2, 4] == Some [1, 2]

test "a handler around map, stopping" := halveAll [2, 3] == None

def halveEach (numbers: List Nat): List (Option Nat) := numbers.map (x => Abort.toOption (() => half x))

test "a handler in map's callback" := halveEach [2, 3] == [Some 1, None]

def halveEachResult (numbers: List Nat): List (Result Nat Text) :=
  numbers.map (x => Fail.toResult (() => halfOrFail x))

test "another handler in map's callback" := halveEachResult [2, 3] == [Ok 1, Err "odd"]

def quarterAll (numbers: List Nat): Result (Option (List Nat)) Text :=
  Fail.toResult (() => Abort.toOption (() => numbers.map (x => halfOrFail (half x))))

test "two handlers around map" := quarterAll [4, 8] == Ok (Some [1, 2])

test "two handlers around map, stopping" := quarterAll [4, 3] == Ok None

test "two handlers around map, failing" := quarterAll [4, 2] == Err "odd"

def halvedCount (numbers: List Nat): Nat := match Abort.toOption (() => numbers.map half) with
  | Some halves => List.length halves
  | None => 0

test "a handler matched on" := halvedCount [2, 4] == 2

-- The reviewer's probe for the case stage 3 excluded handlers for.
theorem thenLaw (first: () → {Abort} a) (rest: a → {Abort} b):
    Abort.toOption (() => rest (first ())) =
      Option.flatMap (Abort.toOption first) (x => Abort.toOption (() => rest x)) :=
  match reify first with
    | return x => rfl
    | Abort.stop (), _ => rfl
