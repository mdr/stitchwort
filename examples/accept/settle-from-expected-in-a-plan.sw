-- A call whose settled type argument is wrong (the goal's `Char` against
-- `natSrc`'s `Nat`, fine once `Ph` is unfolded) inside a call whose own
-- expected type is used first: the body is elaborated again with nothing
-- settled, so it is accepted as it would be without settling (SW-3311).
import Std (Nat, Char)

ability Src (t: Type) where
  next: () → {Src t} t

def Ph (u: Type) (n: Nat): Prop := n = n

theorem ph ∀ (p: () → {Src t} a) (n: Nat): Ph t n := rfl

def natSrc(): {Src Nat} Nat := Src.next()

def double (n: Nat): Nat := n + n

theorem wrap ∀ [k: Nat] (y: double k <= 0) (x: Ph Char k): Ph Char k := x

theorem wrapped: Ph Char 0 := wrap (Nat.leRefl 0) (ph natSrc 0)
