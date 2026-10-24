-- expect-error: E-INTERNAL
-- A program can't build a row: `Effect.Effects`'s constructors are internal to
-- the standard library (docs/proposals/effect-polymorphism.md §5.C.2,
-- D1122). Otherwise it could write `Ops NoOp NoRes`, a second empty row that
-- computes differently from `Empty`, or a row repeating an ability.
import Std (List, Effect)

def explicitRow (xs: List Nat): List Nat :=
  List.mapIn [e := Effect.Effects.Empty] (x => x + 1) xs
