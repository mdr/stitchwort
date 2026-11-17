-- A tuple pattern takes apart a whole chain of `&&` at once: the parts after
-- the first are test facts again, and a nested tuple pattern reads them as
-- `∧` in turn, as `Both ha (Both hb hc)` does (SW-3740). Each name is the
-- part's test fact; `.read` turns it into what it says.
import Std (Bool, Nat, List)

theorem third ∀ (x: Nat) (xs: List Nat) (h: (x < 3 && 0 < x && xs.contains x) = True): x ∈ xs :=
  let (_, _, found) := h.read
  found.read

theorem fifth ∀ (x: Nat) (xs: List Nat) (h: (x < 3 && 0 < x && xs.contains x && x < 7 && 1 < x) = True): 1 < x :=
  let (_, _, _, _, last) := h.read
  last.read

-- Without `.read`, the pattern reads the fact itself.
theorem second ∀ (x: Nat) (xs: List Nat) (h: (x < 3 && 0 < x && xs.contains x) = True): 0 < x :=
  let (_, positive, _) := h
  positive.read
