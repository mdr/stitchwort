-- The contraction takes the lambda's implicit binder into account:
-- `(n: Nat) [k: Nat] (x: Nat) => SameK n [k := k] x` is `SameK`, which
-- settles `Rel ?rel ?run` against it by the arguments as `SameK` written
-- bare does.
import Std (Nat)

def SameK (n: Nat) [k: Nat] (x: Nat): Prop := x = x

def Rel (rel: (n: Nat) → [k: Nat] → Nat → Prop) (run: () → Nat): Prop :=
  rel (run ()) [k := 0] (run ()) → rel (run ()) [k := 0] (run ())

theorem anyRel ∀ [rel: (n: Nat) → [k: Nat] → Nat → Prop] (run: () → Nat): Rel rel run := h => h

theorem bare: Rel SameK (() => 3) := anyRel _

theorem expanded: Rel ((n: Nat) [k: Nat] (x: Nat) => SameK n [k := k] x) (() => 3) := anyRel _
