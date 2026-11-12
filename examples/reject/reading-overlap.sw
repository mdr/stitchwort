-- expect-error: E-READING-OVERLAP
-- Each test reads as one proposition: a second reading for `small` at
-- `= True` is refused.
import Std (Bool, Nat, Iff)

def small (n: Nat): Bool := n < 10

@[reading]
theorem smallReads (n: Nat): small n ↔ n < 10 := { forward = h => h, backward = h => h }

@[reading]
theorem smallReadsAgain (n: Nat): small n ↔ n ≤ 9 := { forward = h => h, backward = h => h }
