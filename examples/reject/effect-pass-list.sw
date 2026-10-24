-- expect-error: E-REFL
-- A computation passed where a computation is expected, as an item of a list of computations, is
-- passed as it is: an arbitrary computation isn't known to be `Done`. It was
-- run in place and re-wrapped as `Done (runPure c)` before stage 0 of
-- docs/proposals/effect-polymorphism.md, so this checked. The accepted cases
-- are in accept/effect-pass-computations.sw.
import Std (Effect, List)
import Std.Effect.Comp (Done, Call)

def isDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Bool
  | Done value => True
  | Call () rest

def allDone: List (Effect.Comp Effect.NoOp Effect.NoRes Nat) -> Bool
  | Nil => True
  | Cons first rest => isDone first && allDone rest

theorem anyIsDone: (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat) -> allDone [computation] = True := computation => rfl
