-- expect-error: E-ATTRIBUTE
-- A proof field has no property, so this record has no field to cross as.
@[js.unboxed]
type Fact = { holds: 1 + 1 = 2 }
