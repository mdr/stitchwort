-- expect-error: E-SPLIT
-- `split` doesn't take apart a recursive type such as `List`: that's
-- induction, written as recursion.
import Std (List, Nat)

theorem emptyList (xs: List Nat): List.length xs = 0 := split
