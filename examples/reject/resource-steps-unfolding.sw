-- expect-error: E-RESOURCE
-- A proof by computation on a large literal: `count 3000000` recurses three
-- million calls deep, past the checker's limit. The error names the
-- theorem and the definition it was unfolding.
import Std (Eq, Nat)

def count: Nat → Nat
  | Zero => Zero
  | Succ n => Succ (count n)

theorem countBig: count 3000000 = 3000000 := byComputing
