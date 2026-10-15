-- expect-error: E-TERMINATION
-- `Ping` from DESIGN.md §8: a clause that handles the original computation
-- again, instead of resuming it, loops. Rebuilding the matched tree isn't
-- smaller than it.
type PingOp : Type =
  | Ping

type Unit1 : Type =
  | MkUnit

PingRes : PingOp -> Type
PingRes Ping = Unit1

bad : Comp PingOp PingRes a -> a
bad (Done x)      = x
bad (Call o rest) = bad (Call o rest)
