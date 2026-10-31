-- expect-error: E-CANNOT-INFER
-- A generalising `match` whose scrutinee holds a lambda parameter's type,
-- which nothing ever fixes: the `match` waits for it to the end, and is
-- reported as that unknown would be, with no default (D2090).

import Std (List)

def stuck (n: Nat): Nat :=
  let f := r => match List.length [r] with
    | Zero => 0
    | Succ k => k
  n
