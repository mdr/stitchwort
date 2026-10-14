-- expect-error: E-PROP-ELIM
-- Proofs are erased, so data can't depend on which side of `Or` was proved.
type Or (p : Prop) (q : Prop) : Prop =
  | Inl (left : p)
  | Inr (right : q)

which : (p : Prop) -> (q : Prop) -> Or p q -> Nat
which p q (Inl h) = 0
which p q (Inr h) = 1
