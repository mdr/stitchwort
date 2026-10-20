-- expect-error: E-TERMINATION
-- Passing the function being defined to another function hides what it's
-- called on, so it's refused, even though here it would be fine.
import Std.Effect (Comp)

type ChooseOp: Type =
  | Choose

def ChooseRes: ChooseOp -> Type
  | Choose => Bool

def applyTo (f: Comp ChooseOp ChooseRes Nat -> Nat) (c: Comp ChooseOp ChooseRes Nat): Nat := f c

def viaHelper: Comp ChooseOp ChooseRes Nat -> Nat
  | Done x           => x
  | Call Choose rest => applyTo viaHelper (rest True)
