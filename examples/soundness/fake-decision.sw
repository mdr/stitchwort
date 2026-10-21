-- expect-error: E-TYPE-MISMATCH

import Std (Decidable, Nat)

-- `Decidable.fromYes d Trivial` is how a decision becomes a proof. It must not work
-- when the decision is `No`: here `Decidable.IsYes (Nat.decEq 1 2)` computes to `Void`,
-- which `Trivial` doesn't prove.
theorem oneIsTwo: 1 = 2 := Decidable.fromYes (Nat.decEq 1 2) Trivial
