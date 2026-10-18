-- expect-error: E-TERMINATION
-- From the review of docs/proposals/abilities.md: if an infinite `Comp`
-- could be built, the ordinary fold `drain` would turn it into a proof of
-- anything. Every `Comp` must be a finite tree, so `forever` is refused.
import Effect (Comp)

type LaterOp : Type =
  | Later

type Unit1 : Type =
  | MkUnit

type Empty : Type

def LaterRes : LaterOp -> Type
  | Later => Unit1

def drain : Comp LaterOp LaterRes a -> a
  | Done x          => x
  | Call Later rest => drain (rest MkUnit)

def forever (u : Unit1) : Comp LaterOp LaterRes Empty := Call Later (\v => forever u)
