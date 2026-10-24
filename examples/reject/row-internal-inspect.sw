-- expect-error: E-INTERNAL
-- A program can't take a row apart, so an effect-polymorphic function can't
-- behave differently in the empty row (D1122): `Effect.rowOp` is internal to
-- the standard library.
import Std (Effect)

def operationsOf [e: Effect.Effects] (f: Nat -> {e} Nat): Type := Effect.rowOp e
