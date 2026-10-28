-- expect-error: E-TYPE-MISMATCH
-- A recursive dot call whose `decreasing` proof is for the wrong
-- inequality: reported at the proof, as for the prefix form.
import Std (Nat)

type Counter = { start: Nat }

def Counter.down (counter: Counter) (n: Nat): Nat
    decreasing n
:=
  match n with
    | Zero => counter.start
    | Succ k => counter.down k [decreasing := Nat.leSucc k]
