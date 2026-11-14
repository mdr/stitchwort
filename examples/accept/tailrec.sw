-- `@[tailrec]` (docs/proposals/tailrec.md): every recursive call of the
-- definition must be a tail call, one whose result is the definition's
-- result with nothing left to do after it returns. The attribute changes no
-- term; it makes the compiler check the promise, and on JavaScript it
-- guarantees the definition is a loop.
import Std (List, Nat, Option)

-- The arms of a pattern match, an `if`, and a `let` in front of the call.
@[tailrec]
def sumBig: List Nat → Nat → Nat
  | [], acc => acc
  | [x, ..xs], acc =>
    let next := acc + x
    if x > 100 then sumBig xs next else sumBig xs acc

test "sum the big ones" := sumBig [1, 200, 3, 400] 0 == 600

-- A call on the right of `∧` is in tail position too.
@[tailrec]
def allPositive: List Nat → Bool
  | [] => True
  | [x, ..xs] => x > 0 ∧ allPositive xs

test "all positive" := allPositive [1, 2, 3]

test "not all positive" := allPositive [1, 0, 3] == False

-- A number pattern.
@[tailrec]
def countDown: Nat → Nat → Nat
  | 0, acc => acc
  | 1, acc => acc + 1
  | Succ n, acc => countDown n (acc + 2)

test "count down" := countDown 5 0 == 9

-- A `match` on a computed value is lifted out of the definition
-- (`sumHalves.%match1`) and is part of it.
def halve (n: Nat): Option Nat := if n == 0 then None else Some (n / 2)

@[tailrec]
def sumHalves: List Nat → Nat → Nat
  | [], acc => acc
  | [x, ..xs], acc =>
    match halve x with
      | None => sumHalves xs acc
      | Some h => sumHalves xs (acc + h)

test "halves" := sumHalves [0, 10, 7] 0 == 8

-- A definition by `decreasing`.
@[tailrec]
def halfAcc (n acc: Nat): Nat
    decreasing n
:=
  if h: n < 2 then acc else halfAcc (n - 2) (acc + 1)

test "half" := halfAcc 9 0 == 4

-- The local `go` of the usual accumulator pattern.
def reverseOnto (xs: List Nat): List Nat :=
  @[tailrec]
  def go: List Nat → List Nat → List Nat
    | [], acc => acc
    | [y, ..ys], acc => go ys [y, ..acc]
  go xs []

test "local tailrec" := reverseOnto [1, 2, 3] == [3, 2, 1]

-- The attribute may be on its own line, and on an exported definition.
@[tailrec]
export def lengthOnto (xs: List Nat) (n: Nat): Nat := match xs with
  | [] => n
  | [_, ..rest] => lengthOnto rest (n + 1)

test "export" := lengthOnto [5, 6] 0 == 2

-- In effectful code the call must be the last statement of the block.
ability Counter where
  bump: () → {Counter} ()

@[tailrec]
def bumpTimes: Nat → {Counter} ()
  | 0 => ()
  | Succ n =>
    bump()
    bumpTimes n

def countBumps (prog: () → {Counter | e} a): {e} Pair a Nat :=
  let run: Nat → {e} Pair a Nat :=
    handle prog() with
      | return x => n => MkPair x n
      | bump u, k => n => k() (n + 1)
  run 0

test "effectful loop" := Pair.snd (countBumps (u => bumpTimes 7)) == 7

-- Also when the row is open.
@[tailrec]
def repeatCall: Nat → (() → {e} ()) → {e} ()
  | 0, f => ()
  | Succ n, f =>
    f()
    repeatCall n f

test "open row" := Pair.snd (countBumps (u => repeatCall 3 (v => bump()))) == 3
