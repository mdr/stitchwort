-- A call whose settled type argument is wrong (fine once `Ph` is unfolded)
-- as an argument held for after the expected type, whose comparison then
-- fails: the body is elaborated again with nothing settled, so it is
-- accepted as it would be without settling (SW-3311).
import Std (Nat, Char)

ability Src (t: Type) where
  next: () → {Src t} t

def Ph (u: Type) (n: Nat): Prop := n = n

theorem ph ∀ (p: () → {Src t} a) (n: Nat): Ph t n := byComputing

def natSrc(): {Src Nat} Nat := Src.next()

def double (n: Nat): Nat := n + n

theorem outer ∀ [k: Nat] (x: Ph Char k) (m: Nat) (h: double k = m): double k = m := h

theorem held: 0 = 0 := outer (ph natSrc 0) 0 byComputing
