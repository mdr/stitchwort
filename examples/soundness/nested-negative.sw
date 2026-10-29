-- expect-error: E-POSITIVITY
-- A type inside another data type is allowed only at a parameter that type
-- just stores, as `List` stores its elements (accept/nested-data.sw). `Neg`
-- takes its parameter as a function's input, so `Bad` inside `Neg` is
-- `MkBad (Bad → Void)` in disguise, and proves `Void`
-- (docs/proposals/nested-data-types.md §5.1).
import Std (Void)

type Neg (a: Type): Type =
  | MkNeg (consume: a → Void)

type Bad: Type =
  | MkBad (inner: Neg Bad)

-- Not recursive, so it would pass the termination check.
def notBad: Bad → Void
  | MkBad (MkNeg f) => f (MkBad (MkNeg f))

theorem boom: Void := notBad (MkBad (MkNeg notBad))
