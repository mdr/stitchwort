-- expect-error: E-TYPE-MISMATCH
-- A computation passed where a computation is expected, as a dot call's receiver, is
-- passed as it is: an arbitrary computation isn't known to be `Done`. It was
-- run in place and re-wrapped as `Done (runPure c)` before stage 0 of
-- docs/proposals/effect-polymorphism.md, so this checked. The accepted cases
-- are in accept/effect-pass-computations.sw.
import Std (Effect, List)
import Std.Effect.Comp (Done, Call)

def IsDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a → Prop
  | Done value => Unit
  | Call () rest

def Thunk: Type := Effect.Comp Effect.NoOp Effect.NoRes Nat

def Thunk.finished (computation: Thunk): Prop := IsDone computation

theorem anyIsDone: (computation: Thunk) → computation.finished := computation => Trivial
