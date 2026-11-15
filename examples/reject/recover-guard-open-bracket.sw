-- expect-error: E-PARSE
-- A guard's `[` left open runs out at the arm's `=>`, which always ends a
-- guard whose bracket has no partner. That is one syntax error, at the
-- `=>`, and the arm after it is still read.
def h (x: List Nat): Nat := match x with
  | a if a == [
    => 1
  | _ => 2
