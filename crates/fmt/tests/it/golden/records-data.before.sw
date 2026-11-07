-- Records and data types: fields, constructors, updates and patterns.
type Person = { name: Text, age: Nat }

type Sized (a: Type) =
  { items: List a
  , size: Nat
  }

type Shape =
      | Circle (radius: Nat)
      | Square (side: Nat)

def alice: Person := {name = "Alice", age = 30}
def birthday (p: Person): Person := { p |   age = p.age + 1 }
def nameOf: Person -> Text
  | { name, .. } => name
def empty: Person -> Unit
  | {} => ()
