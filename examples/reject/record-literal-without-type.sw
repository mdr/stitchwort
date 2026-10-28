-- expect-error: E-CANNOT-INFER
-- Nothing says which record type this literal is, and two record types in
-- scope have exactly its fields: `({ … }: Person)` is accepted.

type Person = { name: Text, age: Nat }

type Pet = { name: Text, age: Nat }

test "an unannotated literal" := ({ name = "Alice", age = 30 }).age == 30
