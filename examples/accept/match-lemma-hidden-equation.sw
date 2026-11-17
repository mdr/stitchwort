-- SW-1538, match-refinement.md R2: in an arm of `match slot.field with`,
-- the goal has `None` for `slot.field`, but a lemma about `slot` written in
-- the arm still says `slot.field`. The `match` has no name, so it gets a
-- hidden equation when an arm needs one, and the lemma's proof is
-- rewritten along it as for `match field: slot.field with`.
import Std (Nat, Option)

type Slot = { field: Option Nat, size: Nat }

def width (field: Option Nat) (size: Nat): Nat := match field with
  | None => size
  | Some n => n

theorem widthUpTo ∀ (slot: Slot): width slot.field slot.size ≤ width slot.field slot.size + slot.size := arithmetic

theorem doubled ∀ (slot: Slot): width slot.field slot.size ≤ width slot.field slot.size + slot.size :=
  match slot.field with
    | None => widthUpTo slot
    | Some n => arithmetic
