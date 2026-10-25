-- expect-error: E-ARITY
-- A record pattern as a positional argument (in brackets) stops checking
-- when the constructor gains a field, so it never silently changes meaning
-- (docs/proposals/variant-fields.md §4.2); `W { person = { name, .. }, .. }`
-- would still read `person.name`.

type Person = { name: Text, age: Nat }

type Wrap = | W (person: Person) (name: Text)

def nameOf: Wrap → Text
  | W ({ name, .. }) => name
