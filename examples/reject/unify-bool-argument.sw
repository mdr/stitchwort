-- expect-error: E-TYPE-MISMATCH
-- An unknown function applied to `True` isn't found from what it's compared
-- with: `f True` against `double n` could be `_ => double n`, or
-- `b => if b then double n else 0`, or many more, so none is chosen.
import Std (Bool, Nat)

def double (n: Nat): Nat := n + n

theorem atTrue [f: Bool → Nat] [v: Nat] (h: f True = v): f True = v := h

theorem doubleIsFour (n: Nat) (h: double n = 4): double n = 4 := atTrue h
