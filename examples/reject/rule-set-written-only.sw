-- expect-error: E-REWRITE-REPEATEDLY

import Std (Eq, List, Nat)

rules appends := [List.appendAssoc, List.appendNil]

def padded (xs: List Nat): List Nat := xs ++ []

-- A set's rules are looked for only in the goal as written, and the goal
-- shows `padded ys`, not the `ys ++ []` it computes to. Listing
-- `List.appendNil` in the call, or `padded` beside the set, rewrites it
-- (examples/accept/rewrite-repeatedly-sets.sw).
theorem unpadded ∀ (ys: List Nat): padded ys = ys := rewrite repeatedly [appends]
