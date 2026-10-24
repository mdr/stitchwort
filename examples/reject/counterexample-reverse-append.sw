-- expect-error: E-REFL
-- A false statement with a failing proof: the error carries a counterexample,
-- the smallest inputs that make it false, with the two sides at them
-- (docs/proposals/counterexample-search.md, acceptance test 1).
import Std (List)

theorem reverseAppend (xs: List Nat) (ys: List Nat): List.reverse (xs ++ ys) = List.reverse xs ++ List.reverse ys := rfl
