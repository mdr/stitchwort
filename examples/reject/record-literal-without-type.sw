-- expect-error: E-CANNOT-INFER
-- Nothing says which record type this literal is: `({ … } : Person)` is
-- accepted. No type is guessed from the field names.

type Person = { name : Text, age : Nat }

test "an unannotated literal" := ({ name = "Alice", age = 30 }).age == 30
