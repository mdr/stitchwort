-- expect-error: E-UNKNOWN-FIELD
-- In a function with effects, `|>` and the stages of a call bind values the
-- program didn't name; the suggestion to call `Result.traverse` shows `…`
-- for them, not the compiler's name.

import Std (Result)

def checked (value: Nat): Result Nat Text := if value < 8 then Ok value else Err "too big"

def printChecked (values: List Nat): {IO} () :=
  match values.map (value => value + 1) |> .traverse checked with
    | Ok ok => IO.print "all below 8"
    | Err message => IO.print message
