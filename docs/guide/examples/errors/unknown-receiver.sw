type Person = { name: Text, age: Nat }

def names (people: List Person): List Text :=
  let nameOf := person => person.name
  people.map nameOf
