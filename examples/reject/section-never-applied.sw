-- expect-error: E-CANNOT-INFER
-- A method section is a lambda: `.drop 1` is `x => x.drop 1`, and `drop` is
-- looked up in the namespace of `x`'s type. A section whose argument's type
-- isn't known where it's written waits for something to say it (as `g xs`
-- would), but here nothing does: `g` is never applied, so `x`'s type is
-- never known. Piping into it, passing it where a function type is known,
-- or an annotation says what it takes.

def f (xs: List Nat): List Nat :=
  let g := .drop 1
  xs
