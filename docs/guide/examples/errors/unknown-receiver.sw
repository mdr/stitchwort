type Person = { name: Text, age: Nat }

def headcount (people: List Person): Nat :=
  let nameOf := person => person.name
  people.length
