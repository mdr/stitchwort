-- expect-error: E-TERMINATION
-- The `Ping` handler that handles the original computation again instead of
-- resuming it (DESIGN.md §8), split across two definitions (§6.8,
-- example 15): both pass the computation on, rebuilt or unchanged, so it
-- never gets smaller.
-- Neighbour: `countBumps` in accept/mutual.sw, which only resumes `k`.
import Effect (Comp)

type PingOp : Type =
  | Ping

type Unit1 : Type =
  | MkUnit

PingRes : PingOp -> Type
PingRes Ping = Unit1

bad : Comp PingOp PingRes a -> a
bad (Done x)      = x
bad (Call o rest) = again (Call o rest)

again : Comp PingOp PingRes a -> a
again c = bad c
