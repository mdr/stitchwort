-- expect-error: E-TERMINATION
-- From the review of docs/proposals/abilities.md: if an infinite `Comp`
-- could be built, the ordinary fold `drain` would turn it into a proof of
-- anything. Every `Comp` must be a finite tree, so `forever` is refused.
type LaterOp : Type =
  | Later

type Unit1 : Type =
  | MkUnit

type Empty : Type

LaterRes : LaterOp -> Type
LaterRes Later = Unit1

drain : Comp LaterOp LaterRes a -> a
drain (Done x)          = x
drain (Call Later rest) = drain (rest MkUnit)

forever : Unit1 -> Comp LaterOp LaterRes Empty
forever u = Call Later (\v -> forever u)
