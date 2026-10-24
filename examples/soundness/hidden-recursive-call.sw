-- expect-error: E-TERMINATION
-- The outer call is on a smaller tree (`rest …`), but its argument hides a
-- call on the original one. Every recursive call is checked. A computation
-- can only be taken apart in a proof, so the function returns a `Prop` and
-- the operation's answer is a `Prop` too.
import Std.Effect (Comp)

type ChooseOp: Type =
  | Choose

def ChooseRes: ChooseOp -> Type
  | Choose => Prop

def hidden: Comp ChooseOp ChooseRes Nat -> Prop
  | Done x           => Unit
  | Call Choose rest => hidden (rest (hidden (Call Choose rest)))
