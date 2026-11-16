-- expect-error: E-REWRITE-REPEATEDLY

import Std (List, Nat)

-- The rules fit nowhere once `List.appendNil` has gone, and what is left,
-- `xs ++ ys = ys ++ xs`, doesn't compute to the same both sides: the message
-- shows it, which rules applied and which never did.
theorem bad ∀ (xs ys: List Nat): (xs ++ []) ++ ys = ys ++ xs := rewrite repeatedly [List.appendNil, List.appendAssoc]
