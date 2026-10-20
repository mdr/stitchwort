-- expect-error: E-POSITIVITY
-- Landin's knot again, with the effectful function in `write`'s argument:
-- the operation type would contain computations over itself.
import Std.Effect (Comp)

type Unit1: Type =
  | MkUnit

type CellOp: Type =
  | Write (f: Unit1 -> Comp CellOp (o => Unit1) Unit1)
