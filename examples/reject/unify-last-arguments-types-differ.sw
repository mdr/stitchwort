-- expect-error: E-TYPE-MISMATCH
-- `?p True` against `t ?g` isn't a pattern, and matching the last arguments
-- would solve `?g: Nat → Nat` with `True`, a `Bool`. Their types differ, so
-- the unifier doesn't pair them, and the comparison fails as a mismatch
-- (SW-919: it used to solve `?g`, and the elaborator crashed applying `True`
-- to `0` in `g 0 = g 0`).
def app [p: Bool → Type] (x: p True): p True := x

def probe (t: (Nat → Nat) → Type) (mk: (g: Nat → Nat) → t g) (use: ∀ (g: Nat → Nat) => t g → g 0 = g 0): Nat :=
  let e := use _ (app (mk _))
  let f: 1 = 1 := e
  0
