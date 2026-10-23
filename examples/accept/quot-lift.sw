-- Quotients compute (docs/proposals/map-equality.md §7.2): `Quot.lift f h
-- (Quot.mk a)` is `f a`, by `rfl`. A definition that's a lift of its
-- argument stays folded on a variable, as one stuck on a `match` does, so a
-- goal shows `observe q`; it's still equal to its body (test A8).
import Std (Eq)

def BoolEq (x: Bool) (y: Bool): Prop := x = y
def QE: Type := Quot Bool BoolEq

def toNat (b: Bool): Nat := if b then 1 else 0

def toNatRespects (x: Bool) (y: Bool) (same: BoolEq x y): toNat x = toNat y :=
  rewrite same in rfl

theorem liftComputes: Quot.lift toNat toNatRespects (Quot.mk True: QE) = 1 := rfl

def observe (q: QE): Nat := Quot.lift toNat toNatRespects q

theorem observeTrue: observe (Quot.mk True) = 1 := rfl

theorem observeIsItsBody (q: QE): observe q = Quot.lift toNat toNatRespects q := rfl

-- Function extensionality from `Quot.sound`, with the evaluation and the
-- rebuilding steps as named definitions (A8; `Quot.funext` itself is for the
-- library, stage 1.4): `rebuild a b (Quot.mk f)` is `f`, by the lift rule
-- and eta.
def Pointwise (a: Type) (b: a -> Type) (f: (x: a) -> b x) (g: (x: a) -> b x): Prop :=
  (x: a) -> f x = g x

def FunQ (a: Type) (b: a -> Type): Type := Quot ((x: a) -> b x) (Pointwise a b)

def evalAt (a: Type) (b: a -> Type) (q: FunQ a b) (x: a): b x :=
  Quot.lift [b := b x] (f => f x) (f g same => same x) q

def rebuild (a: Type) (b: a -> Type) (q: FunQ a b): (x: a) -> b x := x => evalAt a b q x

theorem funext (a: Type) (b: a -> Type) (f: (x: a) -> b x) (g: (x: a) -> b x)
    (h: (x: a) -> f x = g x): f = g :=
  Eq.cong (rebuild a b) (Quot.sound [x := f] [y := g] h)
