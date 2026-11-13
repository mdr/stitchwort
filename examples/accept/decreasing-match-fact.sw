-- In a definition with `decreasing`, a `match` on a value that isn't a
-- variable gives a recursive call in its arms the `match`'s equation,
-- `scrutinee = pattern`, named or not. `auto` and `omega` use it like any
-- other fact; a name (`match found: …`) lets a proof pass it to a lemma.
-- `f.unfold` shows the `match` without it, so a proof about the function
-- can match on the same scrutinee, or rewrite it, as on any other
-- (docs/proposals/decreasing-with-hypothesis.md, stage 2).

import Std (Bool, Eq, Int, List, Nat, Option, Set, Void)

-- Unnamed: `omega` reads `n - k = Succ j` as it stands.
def countUp (n: Nat) (k: Nat): Nat
    decreasing n - k
:= match n - k with
  | Zero => k
  | Succ j => countUp n (k + 1)

theorem countUpUnfolds (n: Nat) (k: Nat): countUp n k = (match n - k with | Zero => k | Succ j => countUp n (k + 1)) :=
  countUp.unfold n k

-- A proof matches on the same scrutinee the definition does.
theorem countUpEnds (n: Nat) (k: Nat) (within: k ≤ n): countUp n k = n
    decreasing n - k
:=
  rewrite countUp.unfold n k in
  match left: n - k with
    | Zero => omega [left, within]
    | Succ j => countUpEnds n (k + 1) (omega [left]) [decreasing := omega [left]]

-- Named, for a lemma: `Set.sizePopMin` turns the equation into the decrease.
def drain (set: Set Nat) (total: Nat): Nat
    decreasing set.size
:= match found: set.popMin with
  | None => total
  | Some (least, rest) => drain rest (total + least) [decreasing := Set.sizePopMin set least rest found]

-- `rewrite` replaces the scrutinee, which no equation's `rfl` depends on.
theorem drainEmpty (set: Set Nat) (total: Nat) (none: set.popMin = None): drain set total = total :=
  rewrite drain.unfold set total, none in rfl

theorem drainStep (set: Set Nat) (total: Nat) (least: Nat) (rest: Set Nat) (popped: set.popMin = Some (least, rest)):
    drain set total = drain rest (total + least) :=
  rewrite drain.unfold set total, popped in rfl

theorem drainGrows (set: Set Nat) (total: Nat): total ≤ drain set total
    decreasing set.size
:=
  rewrite drain.unfold set total in
  match found: set.popMin with
    | None => Nat.leRefl total
    | Some (least, rest) =>
      let later := drainGrows rest (total + least) [decreasing := Set.sizePopMin set least rest found]
      omega [later]

-- Under a plain `if`, whose condition the calls get as well.
def drainBelow (bound: Nat) (set: Set Nat) (total: Nat): Nat
    decreasing set.size
:=
  if bound ≤ total then total
  else
    match found: set.popMin with
      | None => total
      | Some (least, rest) => drainBelow bound rest (total + least) [decreasing := Set.sizePopMin set least rest found]

theorem drainBelowOver (bound: Nat) (set: Set Nat) (total: Nat) (under: Nat.leq bound total = False):
    drainBelow bound set total
      = (match set.popMin with
        | None => total
        | Some (least, rest) => drainBelow bound rest (total + least)) :=
  rewrite drainBelow.unfold bound set total, under in rfl

-- A plain `if` in an arm, whose condition the call's proof uses: shown
-- plain too.
def drainWhile (bound: Nat) (set: Set Nat) (total: Nat): Nat
    decreasing bound - total
:= match set.popMin with
  | None => total
  | Some (least, rest) => if total < bound then drainWhile bound rest (total + least + 1) else total

theorem drainWhileStep (bound: Nat) (set: Set Nat) (total: Nat) (least: Nat) (rest: Set Nat)
    (popped: set.popMin = Some (least, rest)) (more: total < bound):
    drainWhile bound set total = drainWhile bound rest (total + least + 1) :=
  rewrite drainWhile.unfold bound set total, popped in
  match fits: total < bound with
    | True => rfl
    | False => Void.exfalso (omega [more, fits])

-- A `match` in an arm of another: the inner call's proof reads both
-- equations, and the plain form is made for both, the inner one first.
def countBoth (n: Nat) (m: Nat) (k: Nat): Nat
    decreasing n - k
:= match n - k with
  | Zero => k
  | Succ j =>
    match m - k with
      | Zero => k
      | Succ _ => countBoth n m (k + 1)

theorem countBothStep (n: Nat) (m: Nat) (k: Nat) (j: Nat) (i: Nat) (outer: n - k = Succ j) (inner: m - k = Succ i):
    countBoth n m k = countBoth n m (k + 1) :=
  rewrite countBoth.unfold n m k, outer, inner in rfl

-- Two scrutinees: each is an expression, so each has an equation.
def countTwo (n: Nat) (m: Nat) (k: Nat): Nat
    decreasing n - k
:= match n - k, m - k with
  | Succ _, Succ _ => countTwo n m (k + 1)
  | _, _ => k

theorem countTwoStep (n: Nat) (m: Nat) (k: Nat) (i: Nat) (j: Nat) (first: n - k = Succ i) (second: m - k = Succ j):
    countTwo n m k = countTwo n m (k + 1) :=
  rewrite countTwo.unfold n m k, first, second in rfl

-- A `let` only the call's proof uses is gone from `f.unfold` with the
-- equation, so the rewrite works as in `drainStep`.
def drainLet (set: Set Nat) (total: Nat): Nat
    decreasing set.size
:= match found: set.popMin with
  | None => total
  | Some (least, rest) =>
    let fewer := Set.sizePopMin set least rest found
    drainLet rest (total + least) [decreasing := fewer]

theorem drainLetStep (set: Set Nat) (total: Nat) (least: Nat) (rest: Set Nat) (popped: set.popMin = Some (least, rest)):
    drainLet set total = drainLet rest (total + least) :=
  rewrite drainLet.unfold set total, popped in rfl

-- A proof other than the call's uses the unnamed equation (`predOf`'s
-- `omega` argument), so `f.unfold` keeps it: its statement names the
-- `match` to say so, and a `rewrite` of `n - k` would be an `E-REWRITE-MOTIVE`.
def predOf (m: Nat) (positive: 0 < m): Nat := m - 1

def countUsed (n: Nat) (k: Nat): Nat
    decreasing n - k
:= match n - k with
  | Zero => k
  | Succ _ => predOf (n - k) omega + countUsed n (k + 1)

theorem countUsedUnfolds (n: Nat) (k: Nat):
    countUsed n k = (match found: n - k with | Zero => k | Succ _ => predOf (n - k) omega + countUsed n (k + 1)) :=
  countUsed.unfold n k

-- Under a lambda passed to another function the equation stays in
-- `f.unfold` too, because the lifted function is called with it.
def sumTo (n: Nat) (k: Nat): Int
    decreasing n - k
:=
  [1].sumBy (_ => match n - k with | Zero => 1 | Succ _ => 1 + sumTo n (k + 1))

theorem sumToUnfolds (n: Nat) (k: Nat):
    sumTo n k = [1].sumBy (_ => match found: n - k with | Zero => 1 | Succ _ => 1 + sumTo n (k + 1)) :=
  sumTo.unfold n k

-- A pair of measures: the first goes down in the arm, by the equation.
def lexDown (n: Nat) (m: Nat) (k: Nat): Nat
    decreasing (n - k, m)
:= match n - k with
  | Zero => m
  | Succ _ => lexDown n m (k + 1)

theorem lexDownStep (n: Nat) (m: Nat) (k: Nat) (j: Nat) (left: n - k = Succ j):
    lexDown n m k = lexDown n m (k + 1) :=
  rewrite lexDown.unfold n m k, left in rfl

-- A call in a pattern guard gets the equation too.
def countGuard (n: Nat) (k: Nat): Nat
    decreasing n - k
:= match n - k with
  | Zero => k
  | Succ _ if countGuard n (k + 1) == n => n
  | Succ _ => k

theorem countGuardZero (n: Nat) (k: Nat) (zero: n - k = Zero): countGuard n k = k :=
  rewrite countGuard.unfold n k, zero in rfl

test "countUp" := countUp 10 3 == 10
test "drain" := drain [3, 1, 2].toSet 0 == 6
test "drainBelow" := drainBelow 2 [3, 1, 2].toSet 0 == 3
test "drainWhile" := drainWhile 3 [3, 1, 2].toSet 0 == 5
test "countBoth" := countBoth 5 4 0 == 4
test "countTwo" := countTwo 5 3 0 == 3
test "drainLet" := drainLet [3, 1, 2].toSet 0 == 6
test "countUsed" := countUsed 3 0 == 6
test "sumTo" := sumTo 3 0 == 4
test "lexDown" := lexDown 3 7 0 == 7
test "countGuard" := countGuard 4 0 == 4
