-- expect-error: E-RECORD-FIELD
-- A record pattern names every field, or ends with `..`, as
-- `nameOf { name, .. }` in examples/accept/records.sw does.

type Person = { name : Text, age : Nat }

nameOf : Person -> Text
nameOf { name } = name
