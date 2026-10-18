-- expect-error: E-CANNOT-INFER
-- A method section is a lambda: `.drop 1` is `\x => x.drop 1`, and `x`'s type
-- must be known where it's checked. A `let` gives it nothing to go on; piping
-- into it, passing it where a function type is known, or an annotation does.

def f (xs : List Nat) : List Nat :=
  let g := .drop 1
  g xs
