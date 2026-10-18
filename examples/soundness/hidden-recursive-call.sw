-- expect-error: E-TERMINATION
-- The outer call is on a smaller tree (`rest …`), but its argument hides a
-- call on the original one. Every recursive call is checked.
import Effect (Comp)

type ChooseOp : Type =
  | Choose

def ChooseRes : ChooseOp -> Type
  | Choose => Bool

def hidden : Comp ChooseOp ChooseRes Nat -> Nat
  | Done x           => x
  | Call Choose rest => hidden (rest (Nat.leq (hidden (Call Choose rest)) 0))
