-- expect-error: E-OMEGA
-- A fact given to `omega` in brackets that isn't arithmetic is named in a
-- note on the failure, not dropped silently.

import Std (Nat, List)

theorem unusable (x: Nat) (xs: List Nat) (h: x ∈ xs): x ≤ 0 := omega [h]
