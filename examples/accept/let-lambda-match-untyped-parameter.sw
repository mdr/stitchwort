-- A lambda bound by `let` whose parameter has no written type, and whose
-- body matches a variable from outside the lambda. The parameter's type is
-- unknown while the body is checked, and is the same in every arm:
-- splitting `k` doesn't change it (SW-873), as it doesn't change the
-- lambda's unknown result type (SW-869).

import Std (Option)

-- Pure, on a `Nat`.
def pure (g: Nat → Nat) (k: Nat): Nat :=
  let h :=
    x =>
      match k with
        | 0 => g x
        | n => g (n + x)
  h 1

-- Performing the callback's abilities.
def effects (g: Nat → {e} Nat) (k: Nat): {e} Nat :=
  let h :=
    x =>
      match k with
        | 0 => g x
        | n => g n
  h 1

-- On an `Option`.
def option (g: Nat → Nat) (k: Option Nat): Nat :=
  let h :=
    x =>
      match k with
        | Some m => g (m + x)
        | None => g x
  h 1

-- Two parameters, and two splits, one inside the other.
def nested (j: Nat) (k: Option Nat): Nat :=
  let h :=
    x y =>
      match k with
        | Some m =>
          match j with
            | 0 => m + x
            | _ => m + y
        | None => x + y
  h 1 10

test "pure" := pure (x => x * 2) 0 == 2 ∧ pure (x => x * 2) 5 == 12

test "effects" := effects (x => x * 2) 0 == 2 ∧ effects (x => x * 2) 5 == 10

test "Option" := option (x => x * 2) (Some 3) == 8 ∧ option (x => x * 2) None == 2

test "nested" := nested 0 (Some 5) == 6 ∧ nested 1 (Some 5) == 15 ∧ nested 0 None == 11
