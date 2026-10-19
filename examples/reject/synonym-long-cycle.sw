-- expect-error: E-SYNONYM-CYCLE
-- A longer cycle of synonyms is just as meaningless as a cycle of two.
type A = B
type B = C
type C = A
