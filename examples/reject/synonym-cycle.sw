-- expect-error: E-SYNONYM-CYCLE
-- Two type synonyms defined in terms of each other have no type to stand for.
type A = B
type B = A
