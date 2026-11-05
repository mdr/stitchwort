-- expect-error: E-UNKNOWN-NAME
-- `BirthYear.valid` is a constructor followed by a member of its type, not a
-- name: the note gives the two forms that work (`Key.valid BirthYear` and
-- `BirthYear |> .valid`).

type Key =
  | BirthYear
  | IssueYear

def Key.valid (key: Key) (text: Text): Bool :=
  match key with
    | BirthYear => text.length == 4
    | IssueYear => text.length == 4

def check: Bool := BirthYear.valid "2002"
