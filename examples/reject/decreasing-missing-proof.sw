-- expect-error: E-DECREASING
-- `n / 10 < n` isn't found by `auto` here: the message shows the goal and
-- the hypotheses in scope, and how to give the proof.
import Std (List, Nat)

def digitsOnto (n: Nat) (acc: List Nat): List Nat
  decreasing n
:=
  if big: Nat.leq n 9 = False
  then digitsOnto (n / 10) (Cons (n % 10) acc)
  else Cons n acc
