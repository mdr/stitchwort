-- expect-error: E-TERMINATION
-- Passing the function being defined to another function hides what it's
-- called on, so it's refused, even though here it would be fine.
type ChooseOp : Type =
  | Choose

ChooseRes : ChooseOp -> Type
ChooseRes Choose = Bool

applyTo : (Comp ChooseOp ChooseRes Nat -> Nat) -> Comp ChooseOp ChooseRes Nat -> Nat
applyTo f c = f c

viaHelper : Comp ChooseOp ChooseRes Nat -> Nat
viaHelper (Done x)           = x
viaHelper (Call Choose rest) = applyTo viaHelper (rest True)
