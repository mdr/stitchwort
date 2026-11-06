-- expect-error: E-TYPE-MISMATCH
-- `lem slot` against `Q None 3 4` is a real mismatch (`5` is not `4`); a failed
-- try along `field` must not leave `n := 3` solved behind it (SW-1604).
import Std (Eq, Nat, Option, Void)

type Slot = { field: Option Nat, size: Nat }

type Q (o: Option Nat) (n: Nat) (m: Nat): Prop = { holds: n = n }

theorem lem [n: Nat] (slot: Slot): Q slot.field n 5 := { holds = rfl }

theorem useNamed (slot: Slot): Q slot.field 3 4 :=
  match field: slot.field with
    | None => lem slot
    | Some k => lem slot

theorem useUnnamed (slot: Slot): Q slot.field 3 4 :=
  match slot.field with
    | None => lem slot
    | Some k => lem slot
