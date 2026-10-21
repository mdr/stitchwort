-- expect-error: E-REWRITE-NOTHING

import Std (Nat)

-- The goal has no `m + n`: `rewrite` looks for the rule's left side and finds nothing.
theorem bad (n: Nat) (m: Nat): n + 0 = n :=
  rewrite Nat.addComm m n
