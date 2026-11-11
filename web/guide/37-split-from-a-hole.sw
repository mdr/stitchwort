import Std (Bool, Void)

-- Start a proof with `?` for the whole body, and let the editor split it.
-- With the cursor on the `?`, the light bulb offers "Split on `b`" and
-- "Split on `c`": a variable for each data type in scope. The hypothesis `h`
-- is a fact, not data, so it isn't offered. "Split on `b`" writes
--
--   theorem andbElim (b c: Bool) (h: andb b c = True): c = True := match b with
--     | False => ?
--     | True => ?
--
-- "Split on `c`" on the second `?` then adds `c` as a new column of that same
-- `match`, instead of nesting another one inside; the other arm gets `_`:
--
--     | False, _ => ?
--     | True, False => ?
--     | True, True => ?
--
-- Each `?` shows its own goal, with `h` already refined for that case, so
-- only the proofs are left to write. A cursor on `b` in the header offers
-- the same split when the body is a single `?`.
def andb (b c: Bool): Bool := match b with
  | True => c
  | False => False

theorem andbElim (b c: Bool) (h: andb b c = True): c = True := match b, c with
  | False, _ => Void.exfalso (Bool.falseNotTrue h)
  | True, False => h
  | True, True => rfl
