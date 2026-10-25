-- expect-error: E-INSTANCE-NONE

import Std (List)

-- A proposition is used where a `Bool` is expected only if something
-- decides it, and functions have no `DecEq` instance.
def sameAs (f: Nat -> Nat) (gs: List (Nat -> Nat)): List (Nat -> Nat) :=
  List.filter gs (g => g = f)
