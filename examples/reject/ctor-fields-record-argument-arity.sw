-- expect-error: E-ARITY
-- After a constructor declared with brackets, a record pattern in braces is
-- its argument. It stops checking when the constructor gains a field, so it
-- never silently changes meaning (docs/proposals/brace-syntax-review.md §5):
-- it is not read as naming the new `name` field.

type Person = { name: Text, age: Nat }

type Wrap = | W (person: Person) (name: Text)

def nameOf: Wrap → Text
  | W { name, .. } => name
