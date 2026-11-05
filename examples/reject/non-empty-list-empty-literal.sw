-- expect-error: E-NONEMPTY-EMPTY
-- Where a `NonEmptyList` is expected, `[]` is refused: it has no element.
import Std (NonEmptyList)

def nothing: NonEmptyList Nat := []
