-- expect-error: E-READING-SHAPE
-- A reading's test is a function applied to the theorem's parameters, each
-- once: `small 5` would fit only one test.
import Std (Bool, Nat, Iff)

def small (n: Nat): Bool := n < 10

@[reading]
theorem smallFive: small 5 ↔ 5 < 10 := { forward = h => h, backward = h => h }
