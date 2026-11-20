-- The contraction doesn't depend on the lambda's codomain mentioning its
-- variable: `n x => SameTy n x`, where `x`'s type is `Ty n`, is `SameTy`,
-- which settles `Rel ?rel ?run` against it by the arguments as `SameTy`
-- written bare does.
import Std (Nat)

def Ty (n: Nat): Type := Nat

def SameTy (n: Nat) (x: Ty n): Prop := x = x

def Rel (rel: (n: Nat) → Ty n → Prop) (run: () → Nat): Prop := rel (run ()) (run ()) → rel (run ()) (run ())

theorem anyRel ∀ [rel: (n: Nat) → Ty n → Prop] (run: () → Nat): Rel rel run := h => h

theorem bare: Rel SameTy (() => 3) := anyRel _

theorem expanded: Rel (n x => SameTy n x) (() => 3) := anyRel _
