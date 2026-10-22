-- expect-error: E-DECREASING
-- `decreasing` isn't supported in a group of definitions that call each
-- other yet.
import Std (Nat)

def ping (n: Nat): Nat
  decreasing n
:=
  if h: n = 0 then 0 else pong (n - 1)

def pong (n: Nat): Nat := if h: n = 0 then 0 else ping (n - 1)
