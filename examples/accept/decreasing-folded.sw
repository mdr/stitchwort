-- A definition with `decreasing` stays folded until something takes it
-- apart, a `case` or a number pattern (here, `Nat.toText`'s): both
-- evaluators unfold it then (crates/driver/tests/differential.rs).

import Std (IO, Nat)

def gcd (a: Nat) (b: Nat): Nat
    decreasing b
:=
  if h: b = 0 then a else gcd b (a % b) [decreasing := Nat.modLess a b h]

def halvings (n: Nat) (count: Nat): Nat
    decreasing n
:=
  let next := n / 2
  if h: next < n then halvings next (count + 1) else count

test "gcd as text" := Nat.toText (gcd 12 18) == "6"
test "halvings" := halvings 100 0 == 7

def main(): {IO} () := IO.print ("gcd: " ++ Nat.toText (gcd 12 18) ++ ", halvings: " ++ Nat.toText (halvings 100 0))
