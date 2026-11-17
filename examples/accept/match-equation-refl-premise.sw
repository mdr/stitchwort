-- SW-1538, match-refinement.md R2: a lemma's premise written in an arm of
-- `match field: slot.field with` still says `slot.field`. `byComputing`
-- can't prove `slot.field = None` by computing, so it rewrites the
-- scrutinee along the `match`'s equation and tries again.
import Std (Nat, Option)

type Slot = { field: Option Nat, size: Nat }

def width (field: Option Nat) (size: Nat): Nat := match field with
  | None => size
  | Some n => n

theorem emptyWidth ∀ (slot: Slot) (empty: slot.field = None): width slot.field slot.size = slot.size := rewrite empty

theorem sizeOrWidth ∀ (slot: Slot): slot.size = slot.size + 0 := match field: slot.field with
  | None => rewrite <- emptyWidth slot byComputing
  | Some n => byComputing
