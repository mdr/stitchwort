-- expect-error: E-REFL
-- Data stays data: `3` and `4` differ, whatever proof the `J` before them
-- holds. Partner: `afterJ` in accept/proof-irrelevance.sw.
import Std (Nat, Void)

def fnEq (n: Nat) (h: Void → Void): (Nat → Nat) = (Nat → Nat) :=
  match n with
    | Zero => byComputing
    | Succ m => byComputing

def applyAt (f: Nat → Nat) (x: Nat): Nat := f x

theorem t15 (n: Nat) (u: Void → Void):
    applyAt (J (y e => y) (x => x) (fnEq n u)) 3 = applyAt (J (y e => y) (x => x) (fnEq n u)) 4 :=
  byComputing
