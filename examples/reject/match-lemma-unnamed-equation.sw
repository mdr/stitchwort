-- expect-error: E-TYPE-MISMATCH
-- SW-1538: in an arm of `match slot.field with`, the goal has `None` for
-- `slot.field`, but a lemma about `slot` written in the arm still says
-- `slot.field`. Had the `match` named its equation (`match field:
-- slot.field with`), the lemma's proof would be rewritten along it; the
-- error says so.
import Std (Nat, Option)

type Slot = { field: Option Nat, size: Nat }

def width (field: Option Nat) (size: Nat): Nat :=
  match field with
    | None => size
    | Some n => n

theorem widthUpTo (slot: Slot): width slot.field slot.size ≤ width slot.field slot.size + slot.size :=
  omega

theorem doubled (slot: Slot): width slot.field slot.size ≤ width slot.field slot.size + slot.size :=
  match slot.field with
    | None => widthUpTo slot
    | Some n => omega
