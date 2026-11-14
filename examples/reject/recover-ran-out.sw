-- expect-error: E-PARSE
-- A `let` whose value runs out at the end of its line is a syntax error,
-- and the definition is still checked past it: the type error on the line
-- after is reported too. Nothing is reported about `a`, whose value is
-- missing, nor about `total`, which uses it.
def f (n: Nat): Nat :=
  let a := n +
  let bad: Nat := "text"
  let total := a * 2 + bad
  total

def usesF: Nat := f 2
