-- A constructor with arguments in any component of a tuple pattern, not just
-- the first: `(Some x, Some y, Some z)`.

import Std (Option)

def sum3: (Option Nat, Option Nat, Option Nat) -> Nat
  | (Some x, Some y, Some z) => x + y + z
  | _ => 0

def sum2: (Option Nat, Option Nat) -> Nat
  | (Some x, Some y) => x + y
  | (None, Some y) => y
  | _ => 0

def inMatch (a: Option Nat) (b: Option Nat) (c: Option Nat): Nat :=
  match (a, b, c) with
    | (Some x, Some y, Some z) => x + y + z
    | _ => 0

def sum3Example: sum3 (Some 1, Some 2, Some 3) = 6 := rfl
