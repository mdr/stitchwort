import Std (NonEmptyList, Set)

-- A group always has someone in it, so its people are a `NonEmptyList`:
-- written with brackets, as a list is, where the type says so.
type Person = { answers: Set Char }
type Group = { people: NonEmptyList Person }

def person (answers: Text): Person := { answers = answers.toList.toSet }

def group: Group := { people = [person "abc", person "bc", person "cd"] }

-- `reduce` starts from the first person: no made-up starting set, no `Option`.
def everyone (group: Group): Set Char := group.people.map .answers |> .reduce Set.intersect

-- `[first, ..rest]` matches every non-empty list, so no `[]` case is needed.
def describe: NonEmptyList Person → Text
  | [only] => "one person"
  | [first, ..rest] => "${rest.length + 1} people"

test "everyone answered c" := everyone group == ['c'].toSet
test "three people" := describe group.people == "3 people"
test "the largest is total" := ([3, 9, 4]: NonEmptyList Nat).maximum == 9
