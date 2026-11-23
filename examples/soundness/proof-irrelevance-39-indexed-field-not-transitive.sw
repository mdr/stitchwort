-- expect-error: E-REFL
-- The one corner where conversion isn't transitive (D3727; the SW-4674
-- Fable review, F1). A match into data on an indexed proposition whose
-- constructor has a proof field is outside rule S, so it computes only on a
-- literal constructor: on a proof definition (`pf`, frozen by rule F) or a
-- variable it stays stuck. `t1` holds by comparing `f`'s arguments (rule I
-- on `s` against the constructor) and `t3` by the literal's branch, yet
-- `t4`, their composite, is refused, as is `n1`. Nothing false is
-- accepted: `t8` proves `t4`'s statement from the other two. This should
-- move to accept once rule S covers such propositions (the follow-up to
-- D3727), and `n1` and `t4` then check by `byComputing`.
import Std (Eq, Nat)

type Q2: Nat → Prop = | MkQ2 (w: 0 = 0): Q2 0

def f (x: Nat): Q2 x → Nat
  | MkQ2 w => 5

def pf: Q2 0 := MkQ2 byComputing

theorem t1 ∀ (s: Q2 0): f 0 s = f 0 (MkQ2 byComputing) := byComputing

theorem t3: f 0 (MkQ2 byComputing) = 5 := byComputing

theorem t8 ∀ (s: Q2 0): f 0 s = 5 := Eq.trans (t1 s) t3

theorem t4 ∀ (s: Q2 0): f 0 s = 5 := byComputing

theorem n1: f 0 pf = 5 := byComputing
