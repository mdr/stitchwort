-- A definition whose `Quot.lift` returns a function has arity 1, so
-- `bumpBy q 3` is the call folded on its lift (`q` isn't a `Quot.mk`) with
-- an argument after it. Compared with the lift written out, the call is
-- unfolded and `3` applied to what it computes to, both by conversion
-- (`byComputing`, the kernel too) and by unification (a hypothesis against
-- the goal).
import Std (Eq)

def BoolEq (x y: Bool): Prop := x = y
def QE: Type := Quot Bool BoolEq

def bump (b: Bool) (n: Nat): Nat := if b then n + 1 else n

def bumpRespects (x y: Bool) (same: BoolEq x y): bump x = bump y := rewrite same

def bumpBy (q: QE): Nat → Nat := Quot.lift [b := Nat → Nat] bump bumpRespects q

theorem computed ∀ (q: QE): bumpBy q 3 = Quot.lift [b := Nat → Nat] bump bumpRespects q 3 := byComputing

theorem unified ∀ (q: QE) (p: Nat → Prop) (h: p (bumpBy q 3)): p (Quot.lift [b := Nat → Nat] bump bumpRespects q 3) := h
