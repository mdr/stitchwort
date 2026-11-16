-- `rewrite repeatedly [rules] then ?` shows what the rules left, as a goal.
import Std (List, Nat)

theorem left ∀ (xs ys: List Nat): (xs ++ []) ++ ys = ys ++ xs := rewrite repeatedly [List.appendNil] then ?
