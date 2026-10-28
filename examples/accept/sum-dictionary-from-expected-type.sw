-- A lemma whose dictionary only the expected type fixes: nothing in
-- `List.sumByZero xs` says the sum is of `Nat`s, so `Add.zero` is found
-- once the comparison with the expected type has said so, and is `0`.
import Std (Add, List)

theorem sumOfZeros (xs: List Nat): List.sumBy xs (x => 0) = 0 := List.sumByZero xs

theorem sumOfZeroInts (xs: List Text): List.sumBy xs (x => (0: Int)) = 0 := List.sumByZero xs

-- The same with the dictionary under a definition of its own.
def zeroOf [auto add: Add c] (unused: Nat): c := Add.zero

theorem zeroOfSame [auto add: Add c] (u: Nat): zeroOf [add := add] u = zeroOf [add := add] u := rfl

theorem zeroOfNat (u: Nat): zeroOf u = (0: Nat) := zeroOfSame u
