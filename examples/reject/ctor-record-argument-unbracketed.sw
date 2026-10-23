-- expect-error: E-PARSE
-- A record pattern as a constructor's later argument is in brackets too:
-- braces name a constructor's fields only right after it.

type Person = { name: Text, age: Nat }

type Entry = | MkEntry (rank: Nat) (person: Person)

def nameOf: Entry -> Text
  | MkEntry r { name, .. } => name
