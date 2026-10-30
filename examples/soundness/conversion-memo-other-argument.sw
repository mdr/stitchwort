-- expect-error: E-REFL
-- lean4#14806 (docs/research/kernel.md C21): a conversion cache closed
-- under transitivity answered pairs it was never asked. In one comparison
-- `f x ≡ g x` holds by their case trees and is remembered; `f y ≡ g x`
-- must still be compared (`y` isn't `x`), not answered from the pair of
-- definitions. The memo is keyed by the exact pair (value.rs, `TreeMemo`).
-- Neighbour: `good` in accept/kernel-2026-neighbours.sw.
def f: Nat → Nat
  | Zero => 0
  | Succ _ => 1

def g: Nat → Nat
  | Zero => 0
  | Succ _ => 1

theorem bad (x y: Nat): (f x, f y) = (g x, g x) := rfl
