-- expect-error: E-TYPE-MISMATCH
-- A parser of the wrong type followed by a lambda that reads a field of
-- the goal's type: with `t` taken from the goal, the parser is blamed;
-- without, `t` would be `Nat` and the lambda's `r.count` would be. Both
-- attempts fail, and the earlier error in the source is given: the
-- lambda's follows from the wrong parser (SW-3311).
import Std (List, Nat)

ability Src (t: Type) where
  next: () → {Src t} t

type Rec = { count: Nat }

def Pt (u: Type) (n: Nat): Prop := List u = List u

theorem lam ∀ (p: () → {Src t} t) (f: t → Nat) (n: Nat): Pt t n := byComputing

def natSrc(): {Src Nat} Nat := Src.next()

theorem counted: Pt Rec 0 := lam natSrc (r => r.count) 0
