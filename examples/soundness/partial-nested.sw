-- expect-error: E-POSITIVITY
-- A data type recursing through `Delay`: `Delay` isn't a data type the
-- positivity check can see into, so a type inside it is a nested
-- occurrence, refused like `List Rose` (docs/proposals/partial.md §8.7).
import Effect (Delay, NoOp, NoRes)

type Bad : Type =
  | MkBad (d : Delay NoOp NoRes Bad)
