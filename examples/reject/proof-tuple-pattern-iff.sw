-- expect-error: E-TYPE-MISMATCH
-- A tuple pattern against a known record type reads as a pair, which a
-- record isn't: `↔` is written `{ forward, backward }`.
theorem iffP (p: Prop) (h: p ↔ p): p → p :=
  let (f, _) := h
  f
