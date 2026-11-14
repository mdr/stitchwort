-- An untyped `let` of an `if` over proofs takes the proposition from its
-- branches, as a typed `let` does (SW-3137; before, `E-UNIVERSE`).

import Std (Nat)

theorem choose ∀ (c: Bool) (p q: 1 = 1): 1 = 1 :=
  let w := if c then p else q
  w

theorem guarded ∀ (n: Nat) (p: 1 = 1): 1 = 1 :=
  let w := if h: n = 0 then p else p
  w

-- Data branches still make a value.
def pick (c: Bool): Nat :=
  let w := if c then 1 else 2
  w

-- A chain of untyped data `if`s checks in time linear in its depth.
def deep (c: Bool): Nat :=
  let x :=
    if c then 1
    else if c then 2
    else if c then 3
    else if c then 4
    else if c then 5
    else if c then 6
    else if c then 7
    else if c then 8
    else if c then 9
    else if c then 10
    else if c then 11
    else if c then 12
    else if c then 13
    else if c then 14
    else if c then 15
    else if c then 16
    else if c then 17
    else if c then 18
    else if c then 19
    else 20
  x

-- A nested `if` of proofs.
theorem nested ∀ (c: Bool) (p: 1 = 1): 1 = 1 :=
  let w := if c then (if c then p else p) else p
  w
