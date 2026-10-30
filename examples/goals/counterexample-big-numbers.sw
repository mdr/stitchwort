-- True statements whose inputs, at a machine word's edge, make huge numbers
-- in few steps (SW-907). A random number is sometimes 2^64 or near it; used
-- as a count of doublings, it doubles a number a million times in the
-- million steps an input may take, and used as an exponent and squared, it
-- makes numbers of gigabytes in a hundred steps. The search charges an
-- operation on a big number a step per machine word, so each such input
-- runs out of steps within its budget: the search finishes in its time,
-- with little memory, and says nothing (crates/driver/tests/counterexamples.rs).
import Std (Nat)

def doubleTimes: (n: Nat) → (count: Nat) → Nat
  | n, Zero => n
  | n, Succ count => doubleTimes (n * 2) count

theorem doubleTimesHalved (n: Nat) (count: Nat): Nat.shiftRight (doubleTimes n count) count = n := ?

-- 2^k by squaring, with `fuel` halvings of `k` before it counts up.
def powTwo: (fuel: Nat) → (k: Nat) → Nat
  | Zero, k => Nat.pow 2 k
  | Succ fuel, k =>
    if k == 0 then 1
    else
      let half: Nat := powTwo fuel (k / 2)
      if k % 2 == 0 then half * half else half * half * 2

theorem powTwoIsPow (fuel: Nat) (k: Nat): powTwo fuel k = Nat.pow 2 k := ?
