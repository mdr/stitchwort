-- `byFacts` judges whether a hypothesis is a fact by its conclusion under
-- its binders. A conclusion only the kernel can judge, a definition stuck
-- on a bound variable (`Small x`, `Fam x`), is judged with those binders
-- in scope: read back without them, its variable had no index in the
-- context (SW-3593), and `Fam x`, which is data, was taken for a fact.

def Small: Nat → Prop
  | 0 => True
  | _ => False

def Fam: Nat → Type
  | 0 => Nat
  | _ => Bool

theorem stuckFact ∀ (step: ∀ (x: Nat) => Small x) (n: Nat): Small n := byFacts

theorem stuckData ∀ (f: ∀ (x: Nat) => Fam x) (a b: Prop) (g: a → b) (h: a): b := byFacts
