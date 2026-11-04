-- expect-error: E-TYPE-MISMATCH
-- A `let`-bound lambda with a comparison is inferred as returning a `Prop`
-- (nothing asked for a `Bool`), so it isn't a `Nat → Bool`: the note
-- suggests the annotation.

def below (limit: Nat) (xs: List Nat): List Nat :=
  let small := (x: Nat) => x < limit
  xs.takeWhile small
