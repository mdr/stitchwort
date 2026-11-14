import Std (Bool, Void)

-- Start a proof with `?` for the whole body, and let the editor split it.
-- With the cursor on the `?`, the light bulb offers "Split on `l`" and
-- "Split on `urgent`": a variable for each data type in scope. The
-- hypothesis `h` is a fact, not data, so it isn't offered. "Split on `l`"
-- writes
--
--   theorem goIfUrgent (l: Light) (urgent: Bool) (h: urgent = True):
--       canGo l urgent = True := match l with
--     | Red => ?
--     | Amber => ?
--     | Green => ?
--
-- "Split on `urgent`" on the first `?` then adds `urgent` as a new column
-- of that same `match`, instead of nesting another one inside; the other
-- arms get `_`:
--
--     | Red, False => ?
--     | Red, True => ?
--     | Amber, _ => ?
--     | Green, _ => ?
--
-- Each `?` shows its own goal, with `h` already refined for that case, so
-- only the proofs are left to write. A cursor on `l` in the header offers
-- the same split when the body is a single `?`.
type Light = | Red | Amber | Green

def canGo (l: Light) (urgent: Bool): Bool := match l with
  | Red => urgent
  | Amber => True
  | Green => True

theorem goIfUrgent ∀ (l: Light) (urgent: Bool) (h: urgent = True): canGo l urgent = True := match l, urgent with
  | Red, False => Void.exfalso (Bool.falseNotTrue h)
  | Red, True => rfl
  | Amber, _ => rfl
  | Green, _ => rfl
