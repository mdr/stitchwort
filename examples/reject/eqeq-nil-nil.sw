-- expect-error: E-INSTANCE-UNKNOWN-TYPE
-- `Nil == Nil` doesn't say what the elements are, so there's no `DecEq` to
-- pick (SW-108). Annotating one side, `(Nil: List Nat) == Nil`, settles it.

test "nil nil" := Nil == Nil
