-- A record pattern as a later argument of a constructor is one more
-- argument, whether or not it is bracketed: braces are a constructor's
-- fields only right after a constructor declared with braces.

type Person = { name: Text, age: Nat }

type Entry = | MkEntry (rank: Nat) (person: Person)

def nameOf: Entry → Text
  | MkEntry r { name, .. } => name

def sameName: Entry → Text
  | MkEntry r ({ name, .. }) => name

test "both ways" := nameOf (MkEntry 1 { name = "Ada", age = 36 }) == sameName (MkEntry 2 { name = "Ada", age = 1 })
