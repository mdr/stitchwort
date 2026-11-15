-- expect-error: E-TYPE-MISMATCH
-- Settling `t` from the goal was the mistake (`Ph Nat 0` is `Ph Char 0`
-- once unfolded), and the real slip is `True` given for a `Nat`: the error
-- is the settled attempt's, at `natSrc`, with labels saying where `t` came
-- from and that without it the body fails at `True` (SW-3311).
import Std (Nat, Char, Bool)

ability Src (t: Type) where
  next: () → {Src t} t

def Ph (u: Type) (n: Nat): Prop := n = n

theorem ph ∀ (p: () → {Src t} t) (n: Nat): Ph t n := rfl

def natSrc(): {Src Nat} Nat := Src.next()

theorem wrongNumber: Ph Char 0 := ph natSrc True
