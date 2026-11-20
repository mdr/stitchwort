-- A lambda that only applies a function to its variables is that
-- function: `x y => SameNat x y` is `SameNat`. Facing the unknown `rel`,
-- it settles `Rel ?rel ?run` against `Rel (x y => SameNat x y) (() => 3)`
-- by the arguments, as `SameNat` written bare does; the unfoldings,
-- `?rel (?run ()) …`, can't say what either unknown is.
import Std (Nat)

def SameNat (x y: Nat): Prop := x = y

def Rel (rel: Nat → Nat → Prop) (run: () → Nat): Prop := rel (run ()) (run ()) → rel (run ()) (run ())

theorem anyRel ∀ [rel: Nat → Nat → Prop] (run: () → Nat): Rel rel run := h => h

theorem bare: Rel SameNat (() => 3) := anyRel _

theorem expanded: Rel (x y => SameNat x y) (() => 3) := anyRel _
