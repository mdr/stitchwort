-- expect-error: E-PROP-ELIM
-- Under an enclosing match, as on a parameter, rule S covers only a
-- proposition whose constructor's fields are all proofs: a match into data
-- on a proof field whose proposition has a data field is still refused, so
-- rule S never reads data out of a proof.
import Std (Eq, Nat)

type R: Nat → Prop = | MkR (n: Nat) (w: n = n): R 0

type Outer: Prop = | MkOuter (r: R 0)

def fromData: Outer → Nat
  | MkOuter r =>
    match r with
      | MkR n w => n
