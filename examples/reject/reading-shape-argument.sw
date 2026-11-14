-- expect-error: E-READING-SHAPE
-- A reading's test takes the theorem's parameters themselves: `small (n + 1)`
-- would fit only the tests whose argument is a successor.
import Std (Bool, Nat, Iff)

def small (n: Nat): Bool := n < 10

@[reading]
theorem smallReads (n: Nat): small (n + 1) ↔ n < 9 := { forward = h => h, backward = h => h }
