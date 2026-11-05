-- expect-error: E-NONEMPTY-EMPTY
-- A `NonEmptyList` is never empty, so `[]` can't match one: `[x, ..rest]`
-- alone covers it.
import Std (NonEmptyList)

def first: NonEmptyList Nat → Nat
  | [] => 0
  | [x, ..rest] => x
