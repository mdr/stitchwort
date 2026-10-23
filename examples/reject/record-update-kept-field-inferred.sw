-- expect-error: E-TYPE-MISMATCH
-- The same refusal where the update's type is inferred (a `let`) rather than
-- checked against an expected one: `end` is kept, so `a` stays `Int`, and the
-- new `start` must be an `Int`. The error says which kept field pins `a`.

import Std (Int)

type Timed (a: Type) = { start: a, end: a, label: Text }

def bad (t: Timed Int): Timed Nat :=
  let u := { t | start = Int.toNat t.start }
  u
