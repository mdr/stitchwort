-- expect-error: E-TYPE-MISMATCH
-- A computation passed where a computation is expected, as the argument and the body of a function that takes and returns a computation, is
-- passed as it is: an arbitrary computation isn't known to be `Done`. It was
-- run in place and re-wrapped as `Done (runPure c)` before stage 0 of
-- docs/proposals/effect-polymorphism.md, so this checked. The accepted cases
-- are in accept/effect-pass-computations.sw.
import Std (Effect, List)
import Std.Effect.Comp (Done, Call)

def IsDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a → Prop
  | Done value => Unit
  | Call () rest

def identityComp (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat): Effect.Comp Effect.NoOp Effect.NoRes Nat := computation

theorem anyIsDone: (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat) → IsDone (identityComp computation) := computation => Trivial
