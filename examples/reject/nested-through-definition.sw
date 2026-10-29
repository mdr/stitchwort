-- expect-error: E-POSITIVITY
-- A type may be nested only in a data type, whose constructors say how it
-- uses its parameters: `Children` is a definition, so it isn't looked into.
-- Write `List Tree` (docs/proposals/nested-data-types.md §5.2).
import Std (List)

def Children (a: Type): Type := List a

type Tree: Type =
  | Node (kids: Children Tree)
