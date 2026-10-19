-- expect-error: E-DUPLICATE
-- A record's fields have different names.

type Person = { name: Text, name: Nat }
