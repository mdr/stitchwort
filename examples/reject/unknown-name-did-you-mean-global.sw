-- expect-error: E-UNKNOWN-NAME
-- A misspelt function imported by name: the note suggests the unqualified
-- name that is in scope.
import Std.List (length)

def total: Nat :=
  lenght [1, 2, 3]
