-- expect-error: E-REWRITE-REPEATEDLY-BUDGET

import Std (Nat)

-- `sg` and `sh` apply in turn but never undo each other: the goal walks
-- `g 600`, `h 599`, `g 598`, … down. After 500 rewrites it stops, and says
-- the goal keeps changing rather than that the rules go round in a cycle.
theorem walk ∀ (g h: Nat → Nat)
    (sg: ∀ (n: Nat) => g (n + 1) = h n)
    (sh: ∀ (n: Nat) => h (n + 1) = g n)
    (z: g 0 = 7):
    g 600 = 7 :=
  rewrite repeatedly [sg, sh]
