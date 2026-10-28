-- `let` as an expression: `(let x := e; body)`, with `;` between the value
-- and the body. It makes the same tree as a block `let` followed by the
-- rest, so later parts know the value, a proof may be bound, and a pattern
-- must cover its type. `in` isn't the separator: it is membership.

import Std (List, Nat, Text)

-- A data value, in brackets.
def square (n: Nat): Nat := (let x := n + 1; x * x)

test "square" := square 2 == 9

-- With a type, and a pattern.
def sumPair (p: (Nat, Nat)): Nat := (let (a, b): (Nat, Nat) := p; a + b)

test "sumPair" := sumPair (3, 4) == 7

-- Lets nest, and each later one sees the earlier.
def nested (n: Nat): Nat := (let a := n + 1; let b := a * 2; a + b)

test "nested" := nested 1 == 6

-- Where a lambda is a whole expression: after `:=`, `=>`, `then` and `else`.
def afterAssign (n: Nat): Nat := let d := n * 2; d + 1

def inBranches (b: Bool) (n: Nat): Nat :=
  if b then let d := n + 1; d * d else let e := n + 2; e

def inArm (o: Option Nat): Nat :=
  match o with
    | Some k => let j := k + 1; j * 2
    | None => 0

def inLambda (xs: List Nat): List Nat := xs.map (x => let y := x + 1; y * y)

test "positions" :=
  afterAssign 3 == 7 && inBranches True 1 == 4 && inBranches False 1 == 3
    && inArm (Some 2) == 6 && inLambda [1, 2] == [4, 9]

-- A value that uses `in` membership: the `;` ends it, so `in` stays an
-- operator.
def hasIt (x: Nat) (xs: List Nat): Bool := (let found := x in xs; found)

test "hasIt" := hasIt 2 [1, 2, 3] && !(hasIt 5 [1, 2, 3])

def count (x: Nat) (xs: List Nat): Nat :=
  (let found := x in xs; if found then 1 else 0)

test "count" := count 2 [2] == 1 && count 3 [2] == 0

-- A proof-valued `let`, used by a later expression: the value is known, so
-- `rfl` can see through `p`.
theorem knownValue (n: Nat): n ≤ n + 1 :=
  (let p := n; Nat.leAddRight p 1)

-- `k` is `3` to the checker, so `rfl` proves `k + 1 = 4`.
theorem knownLater: (let k := 3; k + 1) = 4 := rfl

theorem knownInside (n: Nat): n ≤ Succ (Succ n) :=
  (let h := Nat.leSucc n; Nat.leTrans n (Succ n) (Succ (Succ n)) h (Nat.leSucc (Succ n)))

-- The same let as a block gives the same result.
def blockForm (n: Nat): Nat :=
  let x := n + 1
  x * x

theorem sameAsBlock (n: Nat): blockForm n = square n := rfl

-- A body on the next line, inside the brackets.
def twoLines (n: Nat): Nat :=
  (let x := n + 1;
    x * x)

-- A `let` line may carry its body after `;`.
def onALine (n: Nat): Nat :=
  let x := n + 1; x * x
