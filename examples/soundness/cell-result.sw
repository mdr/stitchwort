-- expect-error: E-TERMINATION
-- Landin's knot (`Cell`, DESIGN.md §8): `read` would return an effectful
-- function, so the result type of `Cell`'s operations would have to mention
-- itself. That self-reference isn't a terminating definition.
import Std.Effect (Comp)

type CellOp: Type =
  | Read
  | Write

type Unit1: Type =
  | MkUnit

def CellRes: CellOp -> Type
  | Read  => Unit1 -> Comp CellOp CellRes Unit1
  | Write => Unit1
