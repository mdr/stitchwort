-- A `match` whose expression the search over the computed goal doesn't find
-- refines nothing, even where opening a call would show it written
-- differently: `chainOf more lists` unfolds to `chain (Succ more) lists`,
-- whose body has `lists.map (xs => chainThrough more xs)`, the scrutinee up
-- to eta. Both arms' goals are the goal unchanged, so `found` can still be
-- used to rewrite it. (docs/proposals/partial-unfold.md §3: the middle step
-- never rescues.)
import Std (List, Nat, Option)

def chain (fuel: Nat) (lists: List (List Nat)): Nat := match fuel with
  | Zero => 0
  | Succ more => lists.map (chainThrough more) |> .maximum |> .getOrElse 0

def chainThrough (fuel: Nat): (xs: List Nat) → Nat
  | [] => 0
  | [only] => chain fuel [] + 1
  | [first, ..rest] => 0

def chainOf (more: Nat) (lists: List (List Nat)): Nat := chain (Succ more) lists

theorem bounded ∀ (more: Nat) (lists: List (List Nat)) (cap: Nat): chainOf more lists ≤ cap :=
  match found: lists.map (chainThrough more) |> .maximum with
    | None => ?
    | Some most => ?
