-- expect-error: E-REFL
-- An operand of `=` that is a computation is passed as it is (D1140 (a),
-- docs/proposals/effect-polymorphism.md), and the other side is checked
-- against its type: here that makes it `Done (runPure computation)`, and an
-- arbitrary computation isn't `Done` of its result. Before, the left side
-- was run, so this was `runPure computation = runPure computation` and
-- checked.
-- The accepted cases are in accept/effect-pass-equations.sw.
import Std (Effect, Eq)
import Std.Effect.Comp (Done)

theorem anyIsDone [a: Type] (computation: Effect.Comp Effect.NoOp Effect.NoRes a):
    computation = Effect.runPure computation :=
  rfl
