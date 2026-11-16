-- expect-error: E-REFL
-- SW-1538: `width slot.field 3 = 4` mentions the scrutinee but is false
-- in the `None` arm, so neither error suggests the `match`'s equation.
import Std (Eq, Nat, Option)

type Slot = { field: Option Nat, size: Nat }

def width (field: Option Nat) (size: Nat): Nat :=
  match field with
    | None => size
    | Some n => n

theorem needs (slot: Slot) (w: width slot.field 3 = 4): slot.size = slot.size := byComputing

theorem bad (slot: Slot): slot.size = slot.size :=
  match slot.field with
    | None => needs slot byComputing
    | Some n => byComputing

theorem bad2 (slot: Slot): slot.size = slot.size :=
  match e: slot.field with
    | None => needs slot byComputing
    | Some n => byComputing
