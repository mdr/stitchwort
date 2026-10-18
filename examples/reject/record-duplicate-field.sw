-- expect-error: E-RECORD-FIELD
-- A literal gives each field once.

type Person = { name : Text, age : Nat }

def alice : Person := { name = "Alice", age = 30, name = "Alicia" }
