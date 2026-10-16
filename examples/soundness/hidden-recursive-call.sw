-- expect-error: E-TERMINATION
-- The outer call is on a smaller tree (`rest …`), but its argument hides a
-- call on the original one. Every recursive call is checked.
import Effect (Comp)

type ChooseOp : Type =
  | Choose

ChooseRes : ChooseOp -> Type
ChooseRes Choose = Bool

hidden : Comp ChooseOp ChooseRes Nat -> Nat
hidden (Done x)           = x
hidden (Call Choose rest) = hidden (rest (Nat.leq (hidden (Call Choose rest)) 0))
