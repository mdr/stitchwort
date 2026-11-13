-- An untyped `let` of an `if` over proofs takes the proposition from its
-- branches, as a typed `let` does (SW-3137; before, `E-UNIVERSE`).

import Std (Nat)

theorem choose ∀ (c: Bool) (p: 1 = 1) (q: 1 = 1): 1 = 1 :=
  let w := if c then p else q
  w

theorem guarded ∀ (n: Nat) (p: 1 = 1): 1 = 1 :=
  let w := if h: n = 0 then p else p
  w

-- Data branches still make a value.
def pick (c: Bool): Nat :=
  let w := if c then 1 else 2
  w
