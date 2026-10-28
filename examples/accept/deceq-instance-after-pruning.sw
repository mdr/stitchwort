-- `DecEq.sound a b same`, inside a lambda, solves the `_` of `falseOf` with
-- `==` through `DecEq.sound`'s own dictionary, still to be found. Solving
-- the `_` outside the lambda moves that dictionary's unknown to one that
-- doesn't mention `same`; it is still found, as `Position`'s, and then the
-- result is the `==` of the statement.
import Std (Bool, DecEq, Void)

type Position = { row: Int, column: Int }

theorem falseOf (value: Bool) (refute: value = True → Void): value = False :=
  match value with
    | True => Void.exfalso (refute rfl)
    | False => rfl

theorem notSame (a: Position) (b: Position) (differ: a = b → Void): (a == b) = False :=
  falseOf _ (same => differ (DecEq.sound a b same))
