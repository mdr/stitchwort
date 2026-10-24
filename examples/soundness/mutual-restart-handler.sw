-- expect-error: E-TERMINATION
-- The `Ping` handler that handles the original computation again instead of
-- resuming it (DESIGN.md §8), split across two definitions (§6.8,
-- example 15): both pass the computation on, rebuilt or unchanged, so it
-- never gets smaller.
-- Neighbour: `countBumps` in accept/mutual.sw, which only resumes `k`.
import Std.Effect (Comp)

type PingOp: Type =
  | Ping

type Unit1: Type =
  | MkUnit

def PingRes: PingOp -> Type
  | Ping => Unit1

def bad: Comp PingOp PingRes Nat -> Prop
  | Done x      => Unit
  | Call o rest => again (Call o rest)

def again (c: Comp PingOp PingRes Nat): Prop := bad c
