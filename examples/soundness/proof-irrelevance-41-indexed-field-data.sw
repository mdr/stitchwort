-- expect-error: E-PROP-ELIM
-- Rule S's indexed case with fields (D3727) covers only fields that are
-- proofs, of a proposition that isn't recursive: a match into data on one
-- with a data field, or with a field of its own type, is still refused, so
-- rule S never reads data out of a proof or unfolds without end.
import Std (Eq, Nat)

type R: Nat → Prop = | MkR (n: Nat) (w: n = n): R 0

def fromData (x: Nat): R x → Nat
  | MkR n w => n

type Again: Nat → Prop = | MkAgain (w: 0 = 0) (r: Again 0): Again 0

def fromAgain (x: Nat): Again x → Nat
  | MkAgain w r => 5
