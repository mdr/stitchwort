-- expect-error: E-POSITIVITY
-- `List.Member a xs` is a record whose second parameter's type mentions the
-- first, so the first isn't one a type may be nested in: `[]` here is a
-- `List Q` that doesn't mention `Q` in the checked term (constructors carry
-- no parameters), so nothing would see what it depends on
-- (docs/proposals/nested-data-types.md §5.1 condition 2, §5.5). Nested in
-- `Option`, whose parameter is only stored, it's fine: `Chain` in
-- accept/nested-data-shapes.sw.
import Std (List)

type Q: Type =
  | MkQ (m: List.Member Q [])
