-- Probe for docs/proposals/decidable-record.md §3: an instance for a new type,
-- written test first, as `deriving (DecEq)` would write it. Checks.
import Std (Bool, Nat, Void)

type Dec (p: Prop) = { does: Bool, sound: does = True → p, complete: p → does = True }

type Colour = | Red | Green | Blue

def Colour.same: Colour → Colour → Bool
  | Red, Red => True
  | Green, Green => True
  | Blue, Blue => True
  | x, y => False

theorem Colour.sameSound: (x y: Colour) → Colour.same x y = True → x = y
  | Red, Red, h => rfl
  | Green, Green, h => rfl
  | Blue, Blue, h => rfl
  | Red, Green, h => Void.exfalso (Bool.falseNotTrue h)
  | Red, Blue, h => Void.exfalso (Bool.falseNotTrue h)
  | Green, Red, h => Void.exfalso (Bool.falseNotTrue h)
  | Green, Blue, h => Void.exfalso (Bool.falseNotTrue h)
  | Blue, Red, h => Void.exfalso (Bool.falseNotTrue h)
  | Blue, Green, h => Void.exfalso (Bool.falseNotTrue h)

theorem Colour.sameRefl: (x: Colour) → Colour.same x x = True
  | Red => rfl
  | Green => rfl
  | Blue => rfl

def Colour.decEq (x y: Colour): Dec (x = y) :=
  { does = Colour.same x y, sound = Colour.sameSound x y, complete = h => rewrite h in Colour.sameRefl y }

-- `x == y` would be the test itself, with the colours unknown.
theorem eqIsSame ∀ (x y: Colour): (Colour.decEq x y).does = Colour.same x y := rfl
theorem redIsNotBlue: (Colour.decEq Red Blue).does = False := rfl
