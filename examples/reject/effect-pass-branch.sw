-- expect-error: E-TYPE-MISMATCH
-- A branch of an `if` checked against a computation type written as one is
-- passed as it is (D1140 (a), docs/proposals/effect-polymorphism.md): an
-- arbitrary computation isn't known to be `Done`. Before, the `if` was
-- `Done (if choice then runPure first else runPure second)`, so this checked.
-- The accepted cases are in accept/effect-pass-equations.sw.
import Std (Effect, Bool)
import Std.Effect.Comp (Done, Call)

def IsDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Prop
  | Done value => Unit
  | Call () rest

def pick (choice: Bool) (first second: Effect.Comp Effect.NoOp Effect.NoRes Nat): Effect.Comp Effect.NoOp Effect.NoRes Nat :=
  if choice then first else second

theorem anyIsDone (first second: Effect.Comp Effect.NoOp Effect.NoRes Nat): IsDone (pick True first second) := Trivial
