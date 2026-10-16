-- expect-error: E-RECORD-FIELD
-- A literal gives every field.

type Person = { name : Text, age : Nat }

alice : Person
alice = { name = "Alice" }
