-- A local definition takes the variables it uses as leading parameters in the
-- order they are written (SW-194, D228): the header's parameters, then the
-- arm's pattern variables from left to right. So `reach.left` takes `rest k d`
-- (the order they appear in the arm), then its own argument.

import Std (Nat)

def reach: List Nat → Nat → Nat → Nat → Bool
  | ls, c, Zero, d => c == d
  | [], c, Succ k, d => False
  | [line, ..rest], c, Succ k, d =>
    def left: Nat → Bool
      | Zero => False
      | Succ b => reach rest b k d
    if Nat.leq line c then left c ∨ reach rest (c + 1) k d else reach rest c k d

theorem leftZero ∀ (rest: List Nat) (k d: Nat): reach.left rest k d Zero = False := rfl

theorem leftSucc ∀ (rest: List Nat) (k d b: Nat): reach.left rest k d (Succ b) = reach rest b k d := rfl

theorem reachSplit ∀ (line: Nat) (rest: List Nat) (c k d: Nat)
    (s: Nat.leq line c = True):
    reach [line, ..rest] c (Succ k) d = (reach.left rest k d c ∨ reach rest (c + 1) k d) :=
  rewrite s

-- Header parameters come first, then pattern variables as written, whatever
-- order the case tree splits them in.
def pick (base: Nat): Option Nat → Option Nat → Nat
  | Some x, Some y =>
    def sum: Nat → Nat
      | Zero => x + y + base
      | Succ n => base + n
    sum 0
  | _, _ => base

theorem pickSum ∀ (base x y: Nat): pick.sum base x y Zero = x + y + base := rfl
