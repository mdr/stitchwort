-- expect-error: E-ATTRIBUTE
import Std (Nat)

def f (n: Nat): Nat :=
  @[tailrec]
  let m := n + 1
  m
