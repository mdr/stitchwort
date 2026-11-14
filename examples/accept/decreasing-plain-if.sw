-- In a definition with `decreasing`, a plain `if` gives a recursive call
-- under it its condition: `cond = True` in the `then` branch and its
-- negation in the `else`, for a `Bool` test, or the proposition itself for
-- one such as `a % b < b`. The call's proof (`auto`, then `omega`) can use
-- it without the test being named. `f.unfold` still shows the plain `if`,
-- so proofs about the function see the program as written
-- (docs/proposals/decreasing-with-hypothesis.md, stage 1).

import Std (Bool, Eq, List, Nat)

-- A `Bool` test: `omega` reads `Nat.leq (i + 1) bound = True` as `i + 1 ≤ bound`.
def countUp (bound i: Nat): Nat
    decreasing bound - i
:=
  if Nat.leq (i + 1) bound then countUp bound (i + 1) else i

theorem countUpUnfolds ∀ (bound i: Nat):
    countUp bound i = (if Nat.leq (i + 1) bound then countUp bound (i + 1) else i) :=
  countUp.unfold bound i

theorem countUpDone ∀ (bound i: Nat) (done: Nat.leq (i + 1) bound = False): countUp bound i = i :=
  rewrite countUp.unfold bound i in rewrite done in rfl

-- A proposition: `a % b < b` is the fact the call needs.
def gcd (a b: Nat): Nat
    decreasing b
:=
  if a % b < b then gcd b (a % b) else a

theorem gcdUnfolds ∀ (a b: Nat): gcd a b = (if a % b < b then gcd b (a % b) else a) := gcd.unfold a b

-- A proposition decided other than by a comparison (`Nat.decEq`): `f.unfold`
-- shows the plain `if`.
def countDown (n: Nat): Nat
    decreasing n
:=
  if n = 0 then 0 else 1 + countDown (n - 1)

theorem countDownUnfolds ∀ (n: Nat): countDown n = (if n = 0 then 0 else 1 + countDown (n - 1)) := countDown.unfold n

-- Under another `if`, in an argument, and after a `let`.
def climb (bound i: Nat) (up: Bool): Nat
    decreasing bound - i
:=
  let next := i + 1
  if up then 1 + (if next ≤ bound then climb bound next False else 0)
  else if Nat.leq next bound then climb bound next True
  else 0

theorem climbUnfolds ∀ (bound i: Nat) (up: Bool):
    climb bound i up
      = (if up then 1 + (if i + 1 ≤ bound then climb bound (i + 1) False else 0)
         else if Nat.leq (i + 1) bound then climb bound (i + 1) True
         else 0) :=
  climb.unfold bound i up

-- In an arm of the definition's own `match`.
def sumWhile (bound i: Nat): List Nat → Nat
    decreasing bound - i
  | [] => 0
  | [x, ..xs] => if Nat.leq (i + 1) bound then x + sumWhile bound (i + 1) xs else x

theorem sumWhileUnfolds ∀ (bound i x: Nat) (xs: List Nat):
    sumWhile bound i [x, ..xs] = (if Nat.leq (i + 1) bound then x + sumWhile bound (i + 1) xs else x) :=
  sumWhile.unfold bound i [x, ..xs]

test "countUp" := countUp 10 3 == 10
test "gcd" := gcd 84 36 == 12
test "countDown" := countDown 5 == 5
test "climb" := climb 4 0 True == 3
test "sumWhile" := sumWhile 2 0 [1, 2, 3, 4] == 6
