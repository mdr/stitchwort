-- expect-error: E-ATTRIBUTE
-- Two fields with a property: there is no one value to cross as.
@[js.unboxed]
type Person = { name: Text, age: Nat }
