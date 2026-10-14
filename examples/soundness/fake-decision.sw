-- expect-error: E-TYPE-MISMATCH
-- `fromYes d Trivial` is how a decision becomes a proof. It must not work
-- when the decision is `No`: here `IsYes (decEqNat 1 2)` computes to `Void`,
-- which `Trivial` doesn't prove.
theorem oneIsTwo : 1 = 2
oneIsTwo = fromYes (decEqNat 1 2) Trivial
