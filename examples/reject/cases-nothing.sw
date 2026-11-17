-- expect-error: E-CASES
-- `cases` takes a value of a recursive type such as `List` apart once,
-- but not a part of it again: that's induction, written as recursion.
import Std (List, Nat)

theorem lengthAppendNil ∀ (xs: List Nat): List.length (xs ++ []) = List.length xs := cases
