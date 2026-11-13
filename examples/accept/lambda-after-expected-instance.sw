-- `DecEq.trueOfNe (same => …)` against `(a + a != n) = True`. The lambda's
-- parameter type, `?x = ?y`, comes from the expected type, but the call's own
-- result, `DecEq.decide ?d ?x ?y`, is stuck on a dictionary whose type is
-- unknown too, while the expected type has the instance's method already
-- applied (`Nat.decEq (a + a) n`). The one instance that makes them equal is
-- chosen, so `same` is known when `omega` reads it.
import Std (DecEq)

theorem sumsDiffer ∀ (a b n: Nat) (differ: a ≠ b) (total: a + b = n): ((a + a != n): Bool) = True :=
  DecEq.trueOfNe (same => differ (omega))

-- The same at another type: only `Int`'s instance fits.
theorem intsDiffer ∀ (a b n: Int) (differ: a ≠ b) (total: a + b = n): ((a + a != n): Bool) = True :=
  DecEq.trueOfNe (same => differ (omega))

-- With the type or the operands written, the instance is found as before.
theorem typed ∀ (a b n: Nat) (differ: a ≠ b) (total: a + b = n): ((a + a != n): Bool) = True :=
  DecEq.trueOfNe [a := Nat] (same => differ (omega))

theorem operands ∀ (a b n: Nat) (differ: a ≠ b) (total: a + b = n): ((a + a != n): Bool) = True :=
  DecEq.trueOfNe [x := a + a] (same => differ (omega))
