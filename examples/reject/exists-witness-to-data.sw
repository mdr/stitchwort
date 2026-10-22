-- expect-error: E-PROP-ELIM
-- `Exists` is a proposition: a proof of it can be taken apart to prove another
-- proposition (`Exists.elim`), but its witness can't be returned as data. That
-- would let a proof decide data, and proofs are erased at runtime.

import Std (Exists, Nat)

def witnessOf (h: Exists Nat ((n: Nat) => n * n = 49)): Nat :=
  match h with
    | Witness x p => x
