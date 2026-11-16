-- expect-error: E-REFL

import Std (Nat)

-- `d.sound byComputing` is how a decision becomes a proof: `byComputing` proves that its test
-- is `True`. It must not work when the test is `False`: here
-- `(Nat.decEq 1 2).holds` computes to `False`, which `byComputing` doesn't prove
-- `True`.
theorem oneIsTwo: 1 = 2 := (Nat.decEq 1 2).sound byComputing
