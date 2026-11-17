-- expect-error: E-TYPE-MISMATCH
-- The text pattern fixes the type of `x` to `Text`. `x + 1` then fails on
-- the `Text`, and the error points back at the pattern, though `Text` is
-- not the expected side.
def m: Nat :=
  let f := x => match x with | "a" => x + 1 | _ => 0
  f "b"
