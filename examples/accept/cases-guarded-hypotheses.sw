-- `cases` uses a hypothesis `P → Q` in a case where its premise holds: once
-- `b` is split, `b = True → fact` is `True = True → fact` in the `True`
-- case, and `cases` adds `fact` (SW-948; docs/syntax.md, "cases"). Before,
-- each such proof matched on `b` by hand and wrote `let f := h rfl`.

import Std (Nat)

-- A guarded bound, used by `omega` in the case that needs it.
theorem guardedBound ∀ (b: Bool) (n: Nat) (hb: b = True → n ≤ 3): (b ∧ 4 <= n) = False := cases

-- Two coordinates, each with a guarded fact (AoC 2021 day 5).
theorem combineDiagonal ∀ (ax: Nat) (ay: Nat) (i: Nat) (d: Nat) (hi: i ≤ d) (bx: Bool) (by: Bool) (e: Bool)
    (hx: bx = True → ax ≤ d) (hy: by = True → ay ≤ d) (he: e = True → d = 0):
    ((bx ∧ i == ax) ∧ (by ∧ i == ay)) = ((bx ∧ by ∧ (e ∨ ax == ay)) ∧ i == Nat.max ax ay) :=
  cases

-- A premise a hypothesis states, with nothing split.
theorem givenPremise ∀ (b: Bool) (n: Nat) (known: b = True) (h: b = True → n = 3): (n == 3) = True := cases

-- Chained: the fact added is itself an implication whose premise holds.
theorem chained ∀ (a: Bool) (b: Bool) (n: Nat) (h: a = True → b = True → n = 0) (ha: a = True) (hb: b = True): n = 0 := cases
