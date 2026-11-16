-- expect-error: E-TYPE-MISMATCH
-- A tuple pattern opens a pair, a proof of `∧` or a proof of `∃`; a `∨`
-- has two constructors, so it is taken apart by `Inl` and `Inr`.
theorem orP (p q: Prop) (h: p ∨ q): q ∨ p := match h with
  | (a, b) => Inl b
