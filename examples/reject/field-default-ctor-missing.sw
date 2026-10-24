-- expect-error: E-RECORD-FIELD
-- A named construction may leave out only the fields that have defaults
-- (docs/proposals/named-arguments.md §5.1).

type Shape =
  | Circle (radius: Nat) (id: Text := "anonymous")
  | Square (side: Nat)

def shape: Shape := Circle { id = "a" }
