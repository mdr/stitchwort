-- expect-error: E-TERMINATION
-- From the review of docs/proposals/abilities.md: if an infinite `Comp`
-- could be built, the ordinary fold `drain` would turn it into a proof of
-- anything. Every `Comp` must be a finite tree, so `forever` is refused. A
-- computation can only be built and taken apart in a proof, so both work on
-- `Prop`s here, and `forever` folds the tree it builds.
import Std.Effect (Comp)

type LaterOp: Type =
  | Later

type Unit1: Type =
  | MkUnit

def LaterRes: LaterOp → Type
  | Later => Unit1

def drain: Comp LaterOp LaterRes Prop → Prop
  | Done x          => x
  | Call Later rest => drain (rest MkUnit)

def forever (u: Unit1): Prop := drain (Call Later (v => Done (forever u)))
