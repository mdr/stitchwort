-- expect-error: E-TYPE-MISMATCH
-- `h2` is meant as `Eq.trans`'s second argument, but written at the same
-- indentation as the call it's a statement of its own, so the call is a
-- line that does nothing and `h2` is the whole proof. The error points at
-- the call first, saying so, with a note to indent the argument further
-- (SW-950).

import Std (Eq)

theorem chain (a: Nat) (b: Nat) (c: Nat) (h1: a = b) (h2: b = c): a = c :=
  Eq.trans h1
  h2
