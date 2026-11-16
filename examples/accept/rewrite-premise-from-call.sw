-- A rule with a premise, matched against a call that carries a proof of
-- it (`pick m hm`): the premise is proved as it always was, from a
-- hypothesis or by `arithmetic`, not taken from the call's own proof argument
-- (SW-3529 review). The hash snapshot pins the proof term.
import Std (Bool, Eq, List, Nat)

def pick (n: Nat) (h: n ≠ 0): Nat := n + 1

theorem pickEq ∀ (n: Nat) (h: n ≠ 0): pick n h = n + 1 := byComputing

-- `hm2` has the premise's type and is the later hypothesis.
theorem fromHypothesis ∀ (m: Nat) (hm hm2: m ≠ 0): pick m hm = m + 1 := rewrite pickEq

theorem byOmega ∀ (k: Nat) (hk: Succ k ≠ 0): pick (Succ k) hk = k + 2 := rewrite pickEq

def Good (n: Nat): Prop := n = n

def choose (n: Nat) (h: Good n): Nat := n + 1

theorem chooseEq ∀ (n: Nat) (h: Good n): choose n h = n + 1 := byComputing

theorem good ∀ (k: Nat): Good k := byComputing

-- No hypothesis proves `Good (Succ k)` and `arithmetic` can't: the premise is
-- found by unifying with the rest of the rule.
theorem fromTheCall ∀ (k: Nat): choose (Succ k) (good (Succ k)) = k + 2 := rewrite chooseEq
