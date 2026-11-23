-- Conversion is transitive on an indexed one-constructor proposition
-- whose constructor has a proof field (D3727; the SW-4674 Fable review,
-- F1). Rule S takes the match's branch on any proof whose indices equal the
-- constructor's, its field read as the proof's field: so `f 0 s` is `5` for
-- a variable `s` (`t4`) and for a proof definition `pf`, which rule F
-- freezes (`n1`), as `t1` and `t3` together already said. This holds for a
-- match on one of the definition's parameters; a match on a field bound by
-- an enclosing match (`MkOuter q => match q with …`) is the corner still
-- left, where `g o = 5` is refused though both halves check
-- (docs/reviews/SW-4686-fable-review.md, F1; a follow-up).
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
