-- expect-error: E-READING-SHAPE
-- `tiny` takes no parameters, so `tiny n` unfolds to `small n` before
-- anything reads it: a reading filed under `tiny` could never be found.
import Std (Bool, Nat, Iff)

type Small (n: Nat): Prop = { below: n ≤ 3 }

def small (n: Nat): Bool := n <= 3

def tiny: Nat → Bool := small

@[reading]
theorem tinyReads (n: Nat): tiny n ↔ Small n := {
  forward = h => { below = h },
  backward = r => r.below
}
