-- expect-error: E-REFL
-- A hypothesis no small input satisfies: every input is discarded, nothing is
-- found, and nothing is said (acceptance test 7).
import Std (List)

theorem longLists (xs: List Nat) (h: List.length xs = 50): List.length xs = 0 := rfl
