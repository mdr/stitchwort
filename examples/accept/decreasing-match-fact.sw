-- In a definition with `decreasing`, a `match` on a value that isn't a
-- variable gives a recursive call in its arms the `match`'s equation,
-- `scrutinee = pattern`, named or not. `auto` and `omega` use it like any
-- other fact; a name (`match found: …`) lets a proof pass it to a lemma.
-- `f.unfold` shows the `match` without it, so a proof about the function
-- can match on the same scrutinee, or rewrite it, as on any other
-- (docs/proposals/decreasing-with-hypothesis.md, stage 2).

import Std (Bool, Eq, List, Nat, Option, Set, Void)

-- Unnamed: `omega` reads `n - k = Succ j` as it stands.
def countUp (n: Nat) (k: Nat): Nat
    decreasing n - k
:=
  match n - k with
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
:=
  match found: set.popMin with
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
:=
  match set.popMin with
    | None => total
    | Some (least, rest) => if total < bound then drainWhile bound rest (total + least + 1) else total

theorem drainWhileStep (bound: Nat) (set: Set Nat) (total: Nat) (least: Nat) (rest: Set Nat)
    (popped: set.popMin = Some (least, rest)) (more: total < bound):
    drainWhile bound set total = drainWhile bound rest (total + least + 1) :=
  rewrite drainWhile.unfold bound set total, popped in
  match fits: total < bound with
    | True => rfl
    | False => Void.exfalso (omega [more, fits])

test "countUp" := countUp 10 3 == 10
test "drain" := drain [3, 1, 2].toSet 0 == 6
test "drainBelow" := drainBelow 2 [3, 1, 2].toSet 0 == 3
test "drainWhile" := drainWhile 3 [3, 1, 2].toSet 0 == 5
