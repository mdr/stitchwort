-- expect-error: E-REFL
-- A definition's inert positions are its own leading arguments, never an
-- argument after a `J`. Partner: `afterJ` in accept/proof-irrelevance.sw.
import Std (Nat, Void)

def fnEq (n: Nat) (h: Void → Void): (Nat → Nat) = (Nat → Nat) :=
  match n with
    | Zero => rfl
    | Succ m => rfl

def applyAt (f: Nat → Nat) (x: Nat): Nat := f x

theorem t15 (n: Nat) (u: Void → Void):
    applyAt (J (y e => y) (x => x) (fnEq n u)) 3 = applyAt (J (y e => y) (x => x) (fnEq n u)) 4 :=
  rfl
