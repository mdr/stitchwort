-- expect-error: E-PARSE
-- A call's `(` left open at the end of its line runs out there, and the
-- `let` on the next line, at the block's column, starts a new statement.
-- That is one syntax error, at the gap after the `(`; the statements after
-- it are still read and nothing more is reported.
def g (n: Nat): Nat := n

def f (x: Nat): Nat :=
  g (
  let y := 1
  y
