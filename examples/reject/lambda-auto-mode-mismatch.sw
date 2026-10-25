-- expect-error: E-TYPE-MISMATCH
-- `[auto h: P]` takes an `auto` parameter, not an implicit one: the
-- lambda's parameters must come in the order and kinds of its type's
-- (docs/proposals/lambda-syntax.md §4.3).

import Std (Ord)

def f: [a: Type] → [auto order: Ord a] → a → a := [a: Type] [b: Type] (x: a) => x
