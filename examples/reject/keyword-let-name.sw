-- expect-error: E-PARSE
-- A keyword can't be the name a `let` binds.
def twice (n: Nat): Nat :=
  let with := n + n
  with
