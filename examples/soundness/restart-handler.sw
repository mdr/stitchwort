-- expect-error: E-TERMINATION
-- `Ping` from DESIGN.md §8: a clause that handles the original computation
-- again, instead of resuming it, loops. Rebuilding the matched tree isn't
-- smaller than it.
import Std.Effect (Comp)

type PingOp: Type =
  | Ping

type Unit1: Type =
  | MkUnit

def PingRes: PingOp -> Type
  | Ping => Unit1

def bad: Comp PingOp PingRes Nat -> Prop
  | Done x      => Unit
  | Call o rest => bad (Call o rest)
