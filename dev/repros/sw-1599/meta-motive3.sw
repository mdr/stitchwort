import Std (Eq, Nat, Option, Bool, Void)

type Slot = { field: Option Nat, size: Nat }

def isNone (o: Option Nat): Bool := match o with
  | None => True
  | Some _ => False

type Holds (o: Option Nat) (h: isNone o = True): Prop = { holds: o = None }

theorem lem ∀ (slot: Slot) (k: isNone slot.field = True): Holds slot.field k := match e: slot.field with
  | None => { holds = rfl }
  | Some n => Void.exfalso (Bool.falseNotTrue k)

theorem pfL ∀ (slot: Slot) [auto q: slot.field = None]: isNone slot.field = True := rewrite q in rfl

theorem use ∀ (slot: Slot): slot.field = None → Holds None rfl := match field: slot.field with
  | None => _ => lem slot (pfL slot)
  | Some n => h => Void.exfalso (Option.noneNotSome n (Eq.sym h))
