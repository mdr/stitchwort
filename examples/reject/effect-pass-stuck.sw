-- expect-error: E-TYPE-MISMATCH
-- A computation passed where a computation is expected, as a direct argument that is a call stuck on a variable (probe 4 of the note), is
-- passed as it is: an arbitrary computation isn't known to be `Done`. It was
-- run in place and re-wrapped as `Done (runPure c)` before stage 0 of
-- docs/proposals/effect-polymorphism.md, so this checked. The accepted cases
-- are in accept/effect-pass-computations.sw.
import Std (Effect, List)
import Std.Effect.Comp (Done, Call)

def IsDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Prop
  | Done value => Unit
  | Call () rest

def stuckComp: List Nat -> Effect.Comp Effect.NoOp Effect.NoRes Nat
  | Nil => 0
  | Cons x xs => 1

theorem stuckIsDone: (xs: List Nat) -> IsDone (stuckComp xs) := xs => Trivial
