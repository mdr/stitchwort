-- expect-error: E-UNKNOWN-FIELD
-- A literal gives only the record's fields.

type Person = { name : Text, age : Nat }

def alice : Person := { name = "Alice", age = 30, email = "alice@example.com" }
