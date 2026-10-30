-- expect-error: E-REFL
-- lean4#14806, as a chain: `f x ≡ g x` and `g x ≡ f x` are found first in
-- the same comparison, then `f x ≡ h x`, which is false (`h` gives 2 on a
-- `Succ`). Neighbour: `good` in accept/kernel-2026-neighbours.sw.
def f: Nat → Nat
  | Zero => 0
  | Succ _ => 1

def g: Nat → Nat
  | Zero => 0
  | Succ _ => 1

def h: Nat → Nat
  | Zero => 0
  | Succ _ => 2

theorem bad (x: Nat): (f x, g x, f x) = (g x, f x, h x) := rfl
