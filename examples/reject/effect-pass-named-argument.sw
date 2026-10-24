-- expect-error: E-REFL
-- A computation passed where a computation is expected, as an argument given by name, is
-- passed as it is: an arbitrary computation isn't known to be `Done`. It was
-- run in place and re-wrapped as `Done (runPure c)` before stage 0 of
-- docs/proposals/effect-polymorphism.md, so this checked. The accepted cases
-- are in accept/effect-pass-computations.sw.
import Std (Effect, List)
import Std.Effect.Comp (Done, Call)

def isDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Bool
  | Done value => True
  | Call () rest

def takes (count: Nat) (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat): Bool := isDone computation

theorem anyIsDone: (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat) -> takes (computation := computation) (count := 1) = True := computation => rfl
