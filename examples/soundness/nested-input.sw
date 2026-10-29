-- expect-error: E-POSITIVITY
-- Nesting doesn't hide a negative occurrence: `WithCheck` is inside
-- `Option`, but `Option WithCheck` is a function's input, so a `WithCheck`
-- holds a function that can be applied to the value it's in (`selfCheck`),
-- as in `MkBad (Bad → Void)`. Stored in the option, it's fine: `Stored` in
-- accept/nested-data-shapes.sw (docs/proposals/nested-data-types.md §5.2).
import Std (Bool, Option)

type WithCheck: Type =
  | MkW (check: Option WithCheck → Bool)

def selfCheck: WithCheck → Bool
  | MkW f => f (Some (MkW f))
