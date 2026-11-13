-- A `match` found as written agrees with the search over the computed goal
-- under a field too: here the scrutinee is written two ways inside
-- `(choose …).first`, once up to eta (`xs => chainThrough more xs`), and
-- the `match` found as written replaces both, so both arms are `rfl`.
-- (docs/proposals/match-call-field.md §2.4.)
import Std (Bool, Eq, List, Nat, Option)

def chainThrough (fuel: Nat): (xs: List Nat) → Nat
  | [] => 0
  | [only] => fuel + 1
  | [first, ..rest] => 0

type Pair = { first: Option Nat, second: Option Nat }

def choose (flag: Bool) (a: Option Nat) (b: Option Nat): Pair :=
  if flag then { first = a, second = b } else { first = b, second = a }

theorem underField ∀ (more: Nat) (lists: List (List Nat)) (flag: Bool):
    (choose flag (lists.map (xs => chainThrough more xs) |> .maximum) None).first = (choose flag (lists.map (chainThrough more) |> .maximum) None).first :=
  match found: lists.map (chainThrough more) |> .maximum with
    | None => rfl
    | Some most => rfl
