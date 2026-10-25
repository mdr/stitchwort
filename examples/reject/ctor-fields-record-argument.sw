-- expect-error: E-UNKNOWN-FIELD
-- Braces right after a constructor name its own fields, even when its one
-- field holds a record: the record's fields are matched with
-- `W ({ name, .. })`, or `W { person = { name, .. }, .. }`.

type Person = { name: Text, age: Nat }

type Wrap = | W (person: Person)

def nameOf: Wrap → Text
  | W { name, .. } => name
