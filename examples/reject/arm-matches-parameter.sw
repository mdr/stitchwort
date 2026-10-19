-- expect-error: E-ARM-PARAMETER
-- `w` is named in the header, so it is before the colon and no arm can match
-- it. The fix is to move it after the colon: `def pick: Nat -> Nat -> Nat`.
def pick (w: Nat): Nat -> Nat
  | Zero, y => y
  | Succ _, y => w
