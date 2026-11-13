-- Probe for docs/proposals/decidable-record.md §5.1: deciding membership in a
-- 300-element list with the record, checking only the `Bool`. Checks, in
-- 0.5 s; membership-today.sw, the same fact through today's `Decidable`, 2.2 s.
import Std (Bool, Eq, List, Nat, Void)
type Dec (p: Prop) = { does: Bool, sound: does = True → p, complete: p → does = True }
def decEqNat (m n: Nat): Dec (m = n) :=
  { does = Nat.equal m n, sound = h => Nat.equalSound m n h, complete = h => rewrite h in Nat.equalRefl n }
def Dec.or [p q: Prop] (dp: Dec p) (dq: Dec q): Dec (p ∨ q) := {
  does = dp.does || dq.does,
  sound = h => Dec.orSound dp dq h,
  complete = h => Dec.orComplete dp dq h
}
theorem Dec.orSound ∀ [p q: Prop] (dp: Dec p) (dq: Dec q) (h: (dp.does || dq.does) = True): p ∨ q :=
  match dp, dq with
    | { does = True, sound = s, complete = c }, dq => Inl (s rfl)
    | { does = False, sound = s, complete = c }, { does = True, sound = s2, complete = c2 } => Inr (s2 rfl)
    | { does = False, sound = s, complete = c }, { does = False, sound = s2, complete = c2 } => Void.exfalso (Bool.falseNotTrue h)
theorem Dec.orComplete ∀ [p q: Prop] (dp: Dec p) (dq: Dec q) (h: p ∨ q): (dp.does || dq.does) = True :=
  match dp, dq, h with
    | { does = True, sound = s, complete = c }, dq, h => rfl
    | { does = False, sound = s, complete = c }, { does = True, sound = s2, complete = c2 }, h => rfl
    | { does = False, sound = s, complete = c }, { does = False, sound = s2, complete = c2 }, Inl x => Void.exfalso (Bool.falseNotTrue (c x))
    | { does = False, sound = s, complete = c }, { does = False, sound = s2, complete = c2 }, Inr y => Void.exfalso (Bool.falseNotTrue (c2 y))
def decMem (x: Nat): (xs: List Nat) → Dec (List.Mem x xs)
  | [] => { does = False, sound = e => Void.exfalso (Bool.falseNotTrue e), complete = none => Void.exfalso none }
  | [y, ..ys] => Dec.or (decEqNat y x) (decMem x ys)
theorem far: 299 ∈ List.range 0 300 := (decMem 299 (List.range 0 300)).sound rfl
