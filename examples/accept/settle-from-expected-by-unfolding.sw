-- A lemma whose result's type parameter is also its parser's item type,
-- used where the goal names a different type that the result's definition
-- ignores: the goal's `Char` doesn't fit `natSrc`, but `Ph Nat 0` and
-- `Ph Char 0` unfold to the same thing, so the call is accepted (SW-3305).
import Std (Nat, Char)

ability Src (t: Type) where
  next: () → {Src t} t

def Ph (u: Type) (n: Nat): Prop := n = n

theorem ph ∀ (p: () → {Src t} a) (n: Nat): Ph t n := rfl

def natSrc(): {Src Nat} Nat := Src.next()

theorem usePh: Ph Char 0 := ph natSrc 0
