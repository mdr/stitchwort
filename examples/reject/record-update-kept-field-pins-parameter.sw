-- expect-error: E-RECORD-UPDATE
-- An update may change a type parameter only if every field whose type
-- mentions it is replaced (examples/accept/record-update-type-change.sw).
-- Here `end` is kept, and has type `a`, so `a` stays `Int` and the result
-- can't be a `Timed Nat`.

import Std (Int)

type Timed (a: Type) = { start: a, end: a, label: Text }

def bad (t: Timed Int): Timed Nat := { t | start = Int.toNat t.start }
