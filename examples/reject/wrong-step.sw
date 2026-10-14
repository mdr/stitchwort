-- expect-error: E-TYPE-MISMATCH
-- The recursive call proves the statement for `xs`, not for `Cons x xs`.
theorem appendLength : (xs : List a) -> (ys : List a) ->
    length (append xs ys) = length xs + length ys
appendLength Nil         ys = rfl
appendLength (Cons x xs) ys = appendLength xs ys
