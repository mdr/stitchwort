-- expect-error: E-TYPE-MISMATCH
-- As `match-equation-unknown-motive`, with the unknown inside `pfL slot _`.
import Std (Eq, Nat, Option, Bool, Void)

type Slot = { field: Option Nat, size: Nat }

def isNone (o: Option Nat): Bool :=
  match o with
    | None => True
    | Some _ => False

type Holds (o: Option Nat) (h: isNone o = True): Prop = { holds: o = None }

theorem lem (slot: Slot) (k: isNone slot.field = True): Holds slot.field k :=
  match e: slot.field with
    | None => { holds = byComputing }
    | Some n => Void.impossible (Bool.falseNotTrue k)

theorem pfL (slot: Slot) (q: slot.field = None): isNone slot.field = True :=
  rewrite q then byComputing

theorem use (slot: Slot) (q: slot.size = 0): slot.field = None → Holds None byComputing :=
  match field: slot.field with
    | None => _ => lem slot (pfL slot _)
    | Some n => h => Void.impossible (Option.noneNotSome n (Eq.flipped h))
