-- expect-error: E-UNKNOWN-NAME

import Std (Nat, Decidable)

-- The elaborator wraps the decision of an `if a && b` it has not settled
-- yet in a `let` named `%conj`, which carries the `Bool` the `if` is on and
-- is replaced once the branches are known. Source can't write that name, or
-- a library function that does the same: a decision claiming one `Bool` and
-- computing another would make the checker and the runtime disagree.
def sneaky (t: Nat): Nat :=
  Decidable.elim (Decidable.andTagged False (Nat.decEq t t) (_ => Nat.decEq t t)) (_ => 1) (_ => 2)
