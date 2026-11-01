-- expect-error: E-AUTO-NONE
-- A record of propositions gets a derived decision only when each field can
-- be decided (SW-1015). Nothing decides `Even n` for an unknown `n` (it's
-- defined by recursion, with no decision written for it), so `Checked` has
-- none, and the note says which field stopped it.

import Std (Nat)

def Even: Nat → Prop
  | Zero => Unit
  | Succ Zero => Void
  | Succ (Succ n) => Even n

type Checked (n: Nat): Prop = { small: n < 10, even: Even n }

def isChecked (n: Nat): Bool := if h: Checked n then True else False
