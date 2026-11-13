-- SW-1538: in an arm of `match field: slot.field with`, the goal and the
-- hypotheses have the arm's value where they had `slot.field`, but a term
-- written in the arm doesn't: a lemma about `slot` still says
-- `slot.field`, and so does the equation `field` itself. A proof whose type
-- differs from what's expected only in that is rewritten along the
-- `match`'s equation, either way round.
import Std (Eq, Nat, Option, Void)

type Slot = { field: Option Nat, size: Nat }

def width (field: Option Nat) (size: Nat): Nat := match field with
  | None => size
  | Some n => n

theorem emptyWidth (slot: Slot) (empty: slot.field = None): width slot.field slot.size = slot.size :=
  rewrite empty in rfl

-- The lemma's result has `slot.field` where the arm's goal has `None`.
theorem widthOrSet (slot: Slot) (set: ∀ (n: Nat) => slot.field = Some n → n = slot.size):
    width slot.field slot.size = slot.size := match field: slot.field with
      | None => emptyWidth slot field
      | Some n => set n field

-- The lemma's premise has `slot.field` where the refined hypothesis has
-- `None`.
theorem smallWidth (slot: Slot) (small: slot.size ≤ 5): slot.field = None → width slot.field slot.size ≤ 5 :=
  empty => rewrite emptyWidth slot empty in small

theorem smallSize (slot: Slot) (small: slot.size ≤ 5): slot.field = None → width slot.field slot.size ≤ 5 :=
  match field: slot.field with
    | None => empty => smallWidth slot small empty
    | Some n => empty => Void.exfalso (Option.noneNotSome n (Eq.sym empty))
