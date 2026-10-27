-- expect-error: E-CANNOT-INFER
-- Nothing fixes `x`'s type: no annotation, no pattern, and the lambda is
-- never used.
test "unused" :=
  let same := x => x
  True
