-- expect-error: E-REFL
-- A computation passed where a computation is expected, as a constructor's field, given by position, is
-- passed as it is: an arbitrary computation isn't known to be `Done`. It was
-- run in place and re-wrapped as `Done (runPure c)` before stage 0 of
-- docs/proposals/effect-polymorphism.md, so this checked. The accepted cases
-- are in accept/effect-pass-computations.sw.
import Std (Effect, List)
import Std.Effect.Comp (Done, Call)

def isDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Bool
  | Done value => True
  | Call () rest

type Box =
  | MkBox (content: Effect.Comp Effect.NoOp Effect.NoRes Nat)

def boxDone: Box -> Bool
  | MkBox content => isDone content

theorem anyIsDone: (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat) -> boxDone (MkBox computation) = True := computation => rfl
