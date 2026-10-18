-- expect-error: E-PROP-ELIM
-- Proofs are erased, so data can't depend on which side of `Or` was proved.
type Or (p : Prop) (q : Prop) : Prop =
  | Inl (left : p)
  | Inr (right : q)

def which (p : Prop) (q : Prop) : Or p q -> Nat
  | Inl h => 0
  | Inr h => 1
