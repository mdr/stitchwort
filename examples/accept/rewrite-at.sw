-- `rewrite p at h`: `p` proves `a = b`; every `a` in the type of `h` is
-- replaced by `b`. With `in t`, `h` has the new type in `t`; without, the
-- whole is the rewritten fact. The goal is never searched, so it works where
-- no goal is known, or where the goal has computed past what to rewrite.
-- (docs/syntax.md, "rewrite"; docs/proposals/rewrite-hypothesis.md.)
import Std (Bool, Eq, List, Nat, Void)

-- With `in t`, `h` is rebound: in `t` it is a fact about `b`.
theorem inBody (a: Nat) (b: Nat) (e: a = b) (h: a + 1 = 5): b + 1 = 5 :=
  rewrite e at h in h

-- Without `in`, the rewritten fact itself.
theorem noBody (a: Nat) (b: Nat) (e: a = b) (h: a + 1 = 5): b + 1 = 5 :=
  rewrite e at h

-- A fact whose rewritten type computes away: `1 <= 0` is `False = True`, so
-- the goal has no `0` left to rewrite back, but `h`'s type still has `d`.
theorem nonzeroOfPos (d: Nat) (h: 1 ≤ d): d ≠ 0 :=
  e => Bool.falseNotTrue (rewrite e at h)

-- `<-` uses the equation right to left: `b` becomes `a`.
theorem backwards (a: Nat) (b: Nat) (e: a = b) (h: Succ b = 3): Succ a = 3 :=
  rewrite <- e at h

-- Several rules, left to right, each on what the one before left.
theorem two (a: Nat) (b: Nat) (c: Nat) (e1: a = b) (e2: b = c) (h: a + a = 4): c + c = 4 :=
  rewrite e1, e2 at h

-- Any expression may follow `at` (without `in`): a lemma applied to its
-- arguments, rewritten where it stands.
theorem lemma (n: Nat) (m: Nat) (e: n = m): m + Succ 0 = Succ (m + 0) :=
  rewrite e at Nat.addSucc n 0

-- Where nothing says what to prove: an untyped `let`, the argument of `Eq.sym`.
theorem noGoal (a: Nat) (b: Nat) (e: a = b) (h: a + 1 = 5): 5 = b + 1 :=
  let h2 := rewrite e at h
  Eq.sym h2

theorem underSym (a: Nat) (b: Nat) (e: a = b) (h: a + 1 = 5): 5 = b + 1 :=
  Eq.sym (rewrite e at h)

-- A contradiction: rewrite a hypothesis, then compare it with another.
theorem contradiction (x: Nat) (y: Nat) (e: y = x) (hx: Nat.leq 3 x = True) (hy: Nat.leq 3 y = False): Void :=
  rewrite <- e at hx in Bool.trueNotFalse (Eq.trans (Eq.sym hx) hy)

-- In a `calc` step, the rewritten fact proves the step.
theorem inCalc (a: Nat) (b: Nat) (e: a = b) (h: a = 7): b = 7 :=
  calc b
    _ = 7 := rewrite e at h

-- The goal can be rewritten too, by nesting.
theorem both (f: Nat → Nat) (g: Nat → Nat) (k: (n: Nat) → f n = g n) (a: Nat) (b: Nat) (e: a = b) (h: f a = 2): g b = 2 :=
  rewrite e at h in rewrite <- k b in h

-- `at` is only special where a rule can end: a variable called `at` can
-- start a rule, and is bracketed as an argument inside one.
theorem atAsName (f: Nat → Nat) (at: (n: Nat) → f n = n) (h: f 2 + 1 = 5): 2 + 1 = 5 :=
  rewrite at 2 at h

theorem atBracketed (g: Nat → Nat) (p: (n: Nat) → g n = n) (at: Nat) (h: g at = 3): at = 3 :=
  rewrite p (at) at h
