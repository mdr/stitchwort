-- expect-error: E-REFL
-- A computation passed where a computation is expected, as a constructor's field, given by name, is
-- passed as it is: an arbitrary computation isn't known to be `Done`. It was
-- run in place and re-wrapped as `Done (runPure c)` before stage 0 of
-- docs/proposals/effect-polymorphism.md, so this checked. The accepted cases
-- are in accept/effect-pass-computations.sw.
import Std (Effect, List)
import Std.Effect.Comp (Done, Call)

def isDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Bool
  | Done value => True
  | Call () rest

type Labelled =
  | MkLabelled (label: Nat) (inner: Effect.Comp Effect.NoOp Effect.NoRes Nat)

def labelledDone: Labelled -> Bool
  | MkLabelled label inner => isDone inner

theorem anyIsDone: (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat) -> labelledDone (MkLabelled { label = 1, inner = computation }) = True := computation => rfl
