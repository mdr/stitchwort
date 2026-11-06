-- expect-error: E-REFL
-- SW-1538: a lemma's premise written in an arm of `match field: slot.field
-- with` still says `slot.field`, which `rfl` can't prove is `None`: the
-- error points at the `match`'s equation, which does.
import Std (Nat, Option)

type Slot = { field: Option Nat, size: Nat }

def width (field: Option Nat) (size: Nat): Nat :=
  match field with
    | None => size
    | Some n => n

theorem emptyWidth (slot: Slot) (empty: slot.field = None): width slot.field slot.size = slot.size :=
  rewrite empty in rfl

theorem sizeOrWidth (slot: Slot): slot.size = slot.size + 0 :=
  match field: slot.field with
    | None => rewrite <- emptyWidth slot rfl in rfl
    | Some n => rfl
