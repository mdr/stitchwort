-- expect-warning: W-REWRITE-THEN-COMPUTING
-- expect-warning: W-REWRITE-THEN-REWRITE
-- A goal `rewrite` that ends `then byComputing` warns
-- (W-REWRITE-THEN-COMPUTING): without `then`, `rewrite p` closes the goal by
-- computing already. `rewrite a then rewrite b` warns too
-- (W-REWRITE-THEN-REWRITE): it is `rewrite a, b`. Both have a quick fix. A
-- `rewrite … at h`, a `then` with some other proof, and a bracketed second
-- `rewrite` don't warn; nor does a `rewrite` that ends at a comma, where the
-- `then byComputing` keeps the comma from starting another rule.
import Std (Eq)

theorem closed ∀ (a b: Nat) (h: a = b): a + 1 = b + 1 := rewrite h then byComputing

theorem chained ∀ (a b c: Nat) (h: a = b) (g: b = c): a + 1 = c + 1 := rewrite h then rewrite g

theorem bare ∀ (a b: Nat) (h: a = b): a + 1 = b + 1 := rewrite h

theorem joined ∀ (a b c: Nat) (h: a = b) (g: b = c): a + 1 = c + 1 := rewrite h, g

theorem bracketed ∀ (a b c: Nat) (h: a = b) (g: b = c): a + 1 = c + 1 := rewrite h then (rewrite g then byComputing)

theorem beforeComma ∀ (a b: Nat) (h: a = b): (a + 1 = b + 1) ∧ (a + 2 = b + 2) :=
  (rewrite h then byComputing, rewrite h then byComputing)
