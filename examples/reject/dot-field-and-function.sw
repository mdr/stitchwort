-- expect-error: E-DUPLICATE
-- `p.name` would mean both the field and the function: they can't both
-- exist.

type Person = { name : Text }

def Person.name (p : Person) : Text := "x"
