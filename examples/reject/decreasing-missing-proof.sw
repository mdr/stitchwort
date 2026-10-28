-- expect-error: E-DECREASING
-- `n - step < n` isn't found by `auto` here (and isn't true when `step` is
-- 0): the message shows the goal and the hypotheses in scope, and how to
-- give the proof.
import Std (List, Nat)

def countDown (n: Nat) (step: Nat) (acc: List Nat): List Nat
  decreasing n
:=
  if big: Nat.leq n 9 = False
  then countDown (n - step) step (Cons n acc)
  else Cons n acc
