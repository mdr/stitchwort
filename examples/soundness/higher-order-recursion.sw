-- expect-error: E-TERMINATION
-- Passing the function being defined to another function hides what it's
-- called on, so it's refused, even though here it would be fine.
import Std.Effect (Comp)

type ChooseOp: Type =
  | Choose

def ChooseRes: ChooseOp → Type
  | Choose => Bool

def applyTo (f: Comp ChooseOp ChooseRes Nat → Prop) (c: Comp ChooseOp ChooseRes Nat): Prop := f c

def viaHelper: Comp ChooseOp ChooseRes Nat → Prop
  | Done x           => Unit
  | Call Choose rest => applyTo viaHelper (rest True)
