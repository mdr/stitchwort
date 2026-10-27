-- A `match` inside a lambda, written again in a proof's body: the proof's
-- `match` becomes a helper only once the body is elaborated, and is compared
-- with the program's then, by what it does.

import Std (Eq, List)

def label (xs: List Nat): List Nat :=
  xs.map (n => match n with | Zero => 1 | Succ k => k)

-- As an `Eq.cong` argument.
theorem labelCong (xs: List Nat) (ys: List Nat) (h: xs = ys): label xs = label ys :=
  Eq.cong (zs => List.map zs (n => match n with | Zero => 1 | Succ k => k)) h

-- As a lemma's argument, against the same `match` in the statement.
theorem labelThenSucc (xs: List Nat):
    (label xs).map (m => m + 1) = xs.map (n => (match n with | Zero => 1 | Succ k => k) + 1) :=
  List.mapMap xs (m => m + 1) (n => match n with | Zero => 1 | Succ k => k)

-- In a `rewrite` rule.
theorem labelThenSuccRewritten (xs: List Nat):
    (label xs).map (m => m + 1) = xs.map (n => (match n with | Zero => 1 | Succ k => k) + 1) :=
  rewrite List.mapMap xs (m => m + 1) (n => match n with | Zero => 1 | Succ k => k) in rfl

-- Under `rfl`, with the binders renamed.
theorem labelRefl (xs: List Nat): label xs = xs.map (m => match m with | Zero => 1 | Succ j => j) :=
  let ys := xs
  (rfl : label ys = ys.map (m => match m with | Zero => 1 | Succ j => j))
