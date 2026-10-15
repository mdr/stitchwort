-- expect-error: E-TERMINATION
-- Applying a recursive function field gives a smaller tree, but only the
-- field itself counts: a function that returns the original tree isn't a
-- child of it.
type ChooseOp : Type =
  | Choose

ChooseRes : ChooseOp -> Type
ChooseRes Choose = Bool

loop : Comp ChooseOp ChooseRes Nat -> Nat
loop (Done x)      = x
loop (Call o rest) = loop ((\b -> Call o rest : Bool -> Comp ChooseOp ChooseRes Nat) True)
