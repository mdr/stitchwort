-- expect-error: E-REFL
-- The checker never runs partial code (docs/proposals/partial.md §8.5):
-- conversion doesn't unfold `pfix`, so `collatzSteps 1` isn't `now 0`, even
-- though both finish with 0. Unfolding it would let checking loop forever
-- on a partial function that doesn't finish.
import Std.Effect (now, pfix)

def collatzSteps: Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def settled (n: Nat): {Partial} Nat := 0

theorem same: ((u => collatzSteps 1): () -> {Partial} Nat) = (u => settled 1) := rfl
