-- expect-error: E-UNKNOWN-NAME
-- Only names used as types are bound automatically. `xs` is used as a value,
-- so the misspelling is an error rather than a silent new parameter.
theorem lengthNil (ys: List Nat): List.length xs = List.length xs := rfl
