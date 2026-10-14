-- expect-error: E-UNKNOWN-NAME
-- Only names used as types are bound automatically. `xs` is used as a value,
-- so the misspelling is an error rather than a silent new parameter.
theorem lengthNil : (ys : List Nat) -> length xs = length xs
lengthNil ys = rfl
