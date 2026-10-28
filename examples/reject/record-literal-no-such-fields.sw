-- expect-error: E-CANNOT-INFER
-- A literal with no type known takes the record type with exactly its
-- fields; no record type has just `name` (`Person` also has `age`).

type Person = { name: Text, age: Nat }

test "a literal with too few fields" := ({ name = "Alice" }).name == "Alice"
