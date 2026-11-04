-- expect-error: E-TAILREC
-- Building a list around the call is cheap on some backends, but
-- `@[tailrec]` promises only true tail calls.
import Std (List, Nat)

@[tailrec]
def double: List Nat → List Nat
  | [] => []
  | [x, ..xs] => [x * 2, ..double xs]
