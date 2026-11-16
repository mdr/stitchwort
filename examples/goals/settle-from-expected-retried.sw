-- A body that fails with a settled type argument (the goal's `Char`
-- against `natSrc`'s `Nat`, fine once `Ph` is unfolded) and is elaborated
-- again without it: what is left is a hole, so its goal is shown, not the
-- settled attempt's error (SW-3311).
import Std (Nat, Char)

ability Src (t: Type) where
  next: () → {Src t} t

def Ph (u: Type) (n: Nat): Prop := n = n

theorem ph ∀ (p: () → {Src t} a) (n: Nat): Ph t n := byComputing

def natSrc(): {Src Nat} Nat := Src.next()

def double (n: Nat): Nat := n + n

theorem outer ∀ [k: Nat] (x: Ph Char k) (m: Nat) (h: double k = m): double k = m := h

theorem holed: 0 = 0 := outer (ph natSrc 0) 0 ?
