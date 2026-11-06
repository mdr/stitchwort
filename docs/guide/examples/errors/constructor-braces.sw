type Person = { name: Text, age: Nat }

type Booking = | Guest { person: Person }

def ada: Booking := Guest { name = "Ada", age = 36 }
