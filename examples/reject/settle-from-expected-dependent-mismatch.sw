-- expect-error: E-TYPE-MISMATCH
-- The goal's argument at the type parameter's place isn't a `Type`, and the
-- call doesn't fit for another reason: the error is about that reason, with
-- no row such as `{Src (b => List b)}` made from the goal (SW-3305).
import Std (List, Nat)

ability Src (t: Type) where
  next: () → {Src t} t

def Dep (k: Type 1) (x: k) (n: Nat): Prop := n = n

theorem dep ∀ (p: () → {Src t} a) (n: Nat): Dep Type t n := rfl

def natSrc(): {Src Nat} Nat := Src.next()

theorem useNat: Dep (Type → Type) ((b: Type) => List b) 0 := dep natSrc 1
