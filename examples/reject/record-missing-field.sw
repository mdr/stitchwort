-- expect-error: E-RECORD-FIELD
-- A literal gives every field.

type Person = { name : Text, age : Nat }

def alice : Person := { name = "Alice" }
