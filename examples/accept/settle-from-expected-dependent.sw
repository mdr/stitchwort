-- As settle-from-expected-by-unfolding.sw, where the goal's argument at the
-- type parameter's place isn't even a `Type` (SW-3305).
import Std (List, Nat, Char)

ability Src (t: Type) where
  next: () → {Src t} t

def Dep (k: Type 1) (x: k) (n: Nat): Prop := n = n

theorem dep ∀ (p: () → {Src t} a) (n: Nat): Dep Type t n := byComputing

def natSrc(): {Src Nat} Nat := Src.next()
def charSrc(): {Src Char} Char := Src.next()

theorem useNat: Dep (Type → Type) ((b: Type) => List b) 0 := dep natSrc 0
theorem useChar: Dep (Type → Type) ((b: Type) => List b) 0 := dep charSrc 0
