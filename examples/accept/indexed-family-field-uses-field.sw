-- Matching on a value of an indexed family whose index is a constructor,
-- where a field's type applies a parameter to an earlier field: the
-- fields' types are read in the context of the parameters alone, not the
-- indices.

import Std (Nat, Option)

type Holds (p: Nat → Prop): Option Nat → Prop =
  | HoldsNone: Holds p None
  | HoldsSome (x: Nat) (holds: p x): Holds p (Some x)

theorem holdsSome (p: Nat → Prop) (x: Nat): Holds p (Some x) → p x
  | HoldsSome _ holds => holds
