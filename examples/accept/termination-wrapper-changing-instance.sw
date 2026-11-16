-- A one-field wrapper around a strict part, at a type that changes from
-- call to call, with record eta on every match: `{ only = x }` with `x`
-- inside the matched `only` is smaller (docs/reviews/
-- SW-3376-wrapper-rule-soundness.md §3.1, F1). On an unknown `w` none of
-- those matches is stuck, since a match on a record with eta takes its
-- branch with projections; what stops the kernel unfolding `f t es n w` for
-- ever is the match on the type equation `es n`, outside the chain the rule
-- looks at. reject/termination-wrapper-changing-instance-open.sw shows that
-- it does stop there. The size argument in docs/core.md ("Unfolding policy")
-- is why such a program can't unfold for ever.
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
