type Person = { name: Text, age: Nat }

type Guest = | Guest { person: Person, seat: Nat }

def ada: Guest := Guest { name = "Ada", age = 36 }
