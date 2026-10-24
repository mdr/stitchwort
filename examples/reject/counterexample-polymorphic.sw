-- expect-error: E-REFL
-- A statement about any type is tried at `Nat`, and the note says so
-- (D1157, acceptance test 6).
theorem appendComm [a: Type] (xs: List a) (ys: List a): xs ++ ys = ys ++ xs := rfl
