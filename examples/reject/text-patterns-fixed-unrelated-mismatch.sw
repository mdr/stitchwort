-- expect-error: E-TYPE-MISMATCH
-- The text pattern fixes the type of `f`'s argument to `Text`. The
-- unrelated mismatch below, a `Text` literal where a `Nat` is wanted, has
-- nothing to do with it, so it gets no label pointing at the pattern.
def m (cs: List Char): Nat :=
  let f := match | "a" => 1 | _ => 0
  let g: Nat := "x"
  f cs
