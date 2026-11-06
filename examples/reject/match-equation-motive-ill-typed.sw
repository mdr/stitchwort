-- expect-error: E-TYPE-MISMATCH
-- SW-1538: `lem slot (pfL slot field)` has type `Holds slot.field (pfL …)`,
-- whose proof argument is about `slot.field`: replacing `slot.field` by
-- the arm's `None` there doesn't type-check, so the proof isn't rewritten
-- along `field`, and the mismatch is reported as before.
import Std (Eq, Nat, Option, Bool, Void)

type Slot = { field: Option Nat, size: Nat }

def isNone (o: Option Nat): Bool :=
  match o with
    | None => True
    | Some _ => False

type Holds (o: Option Nat) (h: isNone o = True): Prop = { holds: o = None }

theorem lem (slot: Slot) (k: isNone slot.field = True): Holds slot.field k :=
  match e: slot.field with
    | None => { holds = rfl }
    | Some n => Void.exfalso (Bool.falseNotTrue k)

theorem pfL (slot: Slot) (q: slot.field = None): isNone slot.field = True :=
  rewrite q in rfl

theorem use (slot: Slot) (q: slot.size = 0): slot.field = None → Holds None rfl :=
  match field: slot.field with
    | None => _ => lem slot (pfL slot field)
    | Some n => h => Void.exfalso (Option.noneNotSome n (Eq.sym h))
