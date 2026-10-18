-- expect-error: E-TERMINATION
-- Applying a recursive function field gives a smaller tree, but only the
-- field itself counts: a function that returns the original tree isn't a
-- child of it.
import Effect (Comp)

type ChooseOp : Type =
  | Choose

def ChooseRes : ChooseOp -> Type
  | Choose => Bool

def loop : Comp ChooseOp ChooseRes Nat -> Nat
  | Done x      => x
  | Call o rest => loop ((\b => Call o rest : Bool -> Comp ChooseOp ChooseRes Nat) True)
