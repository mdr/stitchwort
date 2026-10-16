-- expect-error: E-UNKNOWN-FIELD
-- A literal gives only the record's fields.

type Person = { name : Text, age : Nat }

alice : Person
alice = { name = "Alice", age = 30, email = "alice@example.com" }
