-- expect-error: E-POSITIVITY
-- A `Map` is built on a quotient, which isn't a data type: nothing says
-- which of its values are part of which, so a type inside one is refused,
-- unlike one inside a `List` (accept/nested-data.sw;
-- docs/proposals/nested-data-types.md §5.6, map-equality.md §11.2).
import Std (Map, Nat)

type M: Type =
  | MkM (kids: Map Nat M)
