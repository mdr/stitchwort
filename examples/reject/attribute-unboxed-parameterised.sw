-- expect-error: E-ATTRIBUTE
-- No type parameters in stage 1 (D1065).
@[js.unboxed]
type Id (a: Type) = { value: a }
