-- expect-error: E-REFL
-- An operand of `=` that is a computation is passed as it is (D1140 (a),
-- docs/proposals/effect-polymorphism.md): an arbitrary computation isn't
-- `Done` of its result. Before, each side was run, so this was
-- `runPure computation = runPure (Done (runPure computation))` and checked.
-- The accepted cases are in accept/effect-pass-equations.sw.
import Std (Effect, Eq)
import Std.Effect.Comp (Done)

theorem anyIsDone [a: Type] (computation: Effect.Comp Effect.NoOp Effect.NoRes a):
    computation = Done (Effect.runPure computation) :=
  rfl
