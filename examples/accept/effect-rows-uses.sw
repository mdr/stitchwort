-- Everyday uses of the effect-polymorphic `List.mapIn` whose row is inferred
-- (design C of docs/proposals/effect-polymorphism.md, §5.C.1, D1123).
-- SW-430: an instance whose type is stuck on a row unknown waits for the row
-- to be defaulted, and a list literal's dot call is seen to run its callback.
-- SW-432: a computation bound by a `let` keeps its row open until its
-- variable meets the result type.
import Std (List, Fail)

ability Log where
  say: Nat -> {Log} ()

-- Runs a computation that logs, collecting what it said.
def Log.collect (program: () -> {Log} a): Pair a (List Nat) :=
  handle program() with
    | return result => MkPair result []
    | Log.say n, k =>
      let rest := k ()
      MkPair rest.fst (Cons n rest.snd)

-- SW-430: the row of a pure use is decided by defaulting, after which
-- `DecEq (List Nat)` is found.
test "a pure use compared with ==" := [1, 2, 3].mapIn (n => n * n) == [1, 4, 9]

def useFirst: Bool := True

-- A receiver whose type is only known once it's elaborated: the instance
-- waits for the row to be defaulted.
test "a pure use on a computed receiver" :=
  (if useFirst then [1, 2] else [3]).mapIn (n => n * n) == [1, 4]

def halve (n: Nat): {Fail} Nat := if n % 2 == 0 then n / 2 else Fail.fail "odd"

-- The thunk's row is `{Fail}`, from `halve`, so `toResult` returns a
-- `Result (List Nat) Text`.
test "an effectful use, failing" := Fail.toResult (() => [4, 6, 7].mapIn halve) == Err "odd"

test "an effectful use, succeeding" := Fail.toResult (() => [4, 6, 8].mapIn halve) == Ok [2, 3, 4]

-- SW-432: a type that becomes a computation only once an unknown is solved
-- (as in `effect-rows.sw`), bound by a `let` and returned later.
def sayAndDouble (n: Nat): {Log} Nat :=
  say n
  n + n

def ResultOf [r: Type] (f: Nat -> r): Type := r

def Answer: Bool -> Type
  | True => ResultOf sayAndDouble
  | False => Nat

type Tagged (flag: Bool): Type =
  | Tag (n: Nat)

def answerOf: (flag: Bool) -> Nat -> Answer flag
  | True, n => sayAndDouble n
  | False, n => n

def Tagged.number [flag: Bool]: Tagged flag -> Nat
  | Tag n => n

def answer [flag: Bool] (tagged: Tagged flag): Answer flag := answerOf flag tagged.number

def loggedLet (numbers: List (Tagged True)): {Log} (List Nat) :=
  let mapped := List.mapIn answer numbers
  mapped

test "a let-bound effectful use" :=
  Log.collect (() => loggedLet [Tag 3, Tag 4]) == MkPair [6, 8] [3, 4]

-- Used before it's returned.
def loggedLetUsed (numbers: List (Tagged True)): {Log} (List Nat) :=
  let mapped := List.mapIn answer numbers
  say (List.length mapped)
  mapped

test "a let-bound effectful use, used first" :=
  Log.collect (() => loggedLetUsed [Tag 3, Tag 4]) == MkPair [6, 8] [3, 4, 2]

def notLoggedLet (numbers: List (Tagged False)): List Nat :=
  let mapped := List.mapIn answer numbers
  mapped

test "a let-bound pure use" := notLoggedLet [Tag 3, Tag 4] == [3, 4]
