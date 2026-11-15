-- expect-error: E-REFL
-- Pairs with accept/termination-wrapper-changing-instance.sw: on unknowns,
-- `f t es n w` unfolds until the match on the type equation `es n` is stuck,
-- so `rfl` fails at once, saying so, rather than running out of steps
-- (`E-RESOURCE`) as an endless unfolding would.
type P (a: Type) (b: Type) = { fst: a, snd: b }
type R (a: Type) = { only: a }
type TEq (a: Type): Type → Type 1 = | TRefl: TEq a a

def f (t: Nat → Type) (es: (n: Nat) → TEq (t n) (P (t (Succ n)) Nat)) (n: Nat) (w: R (t n)): Nat :=
  m t es n (t n) (t (Succ n)) (es n) TRefl w

def m (t: Nat → Type)
    (es: (n: Nat) → TEq (t n) (P (t (Succ n)) Nat))
    (n: Nat) (a b: Type):
    (e1: TEq a (P b Nat)) → (e2: TEq b (t (Succ n))) → (w: R a) → Nat
  | TRefl, TRefl, w => m2 t es n w

def m2 (t: Nat → Type) (es: (n: Nat) → TEq (t n) (P (t (Succ n)) Nat)) (n: Nat): (w: R (P (t (Succ n)) Nat)) → Nat
  | { only = { fst = x, snd = y } } => f t es (Succ n) { only = x }

theorem z ∀ (t: Nat → Type) (es: (n: Nat) → TEq (t n) (P (t (Succ n)) Nat)) (n: Nat) (w: R (t n)): f t es n w = 0 := rfl
