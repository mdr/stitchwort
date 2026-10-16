-- expect-error: E-CANNOT-INFER
-- `.name` looks the field up in the record's type, which isn't known for a
-- lambda's parameter without an annotation. `\(p : Person) -> p.name` (or a
-- signature) is accepted.

type Person = { name : Text, age : Nat }

-- `a` is whatever the function takes, so it isn't known inside it.
describe : (a -> Text) -> Text
describe f = "a function"

described : Text
described = describe (\p -> p.name)
