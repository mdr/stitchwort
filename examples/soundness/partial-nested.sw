-- expect-error: E-POSITIVITY
-- A data type recursing through `Delay`: `Delay` isn't a data type the
-- positivity check can see into, so a type inside it is refused, unlike one
-- inside `List` (docs/proposals/partial.md §8.7,
-- docs/proposals/nested-data-types.md §5.2). Pairs with accept/nested-data.sw.
import Std.Effect (Delay, NoOp, NoRes)

type Bad: Type =
  | MkBad (d: Delay NoOp NoRes Bad)
