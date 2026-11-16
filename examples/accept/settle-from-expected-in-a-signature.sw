-- A lemma call in a signature whose type matches the goal only once
-- unfolded (`Ph Nat 0` against `Ph Char 0`, where `Ph` doesn't use its
-- type parameter). Signatures aren't elaborated twice, so nothing is
-- settled from expected types there, and the call is accepted (SW-3311).
import Std (Nat, Char)

ability Src (t: Type) where
  next: () → {Src t} t

def Ph (u: Type) (n: Nat): Prop := n = n

theorem ph ∀ (p: () → {Src t} a) (n: Nat): Ph t n := byComputing

def natSrc(): {Src Nat} Nat := Src.next()

def Wrap (p: Ph Char 0): Prop := 0 = 0

theorem wrapped: Wrap (ph natSrc 0) := byComputing

def withWrap (h: Wrap (ph natSrc 0)): Nat := 0
