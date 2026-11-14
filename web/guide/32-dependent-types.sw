-- A type can mention a value. `Vec a n` is a list of exactly `n` elements,
-- so the compiler knows lengths and rules out whole classes of mistakes.
import Std (Vec)

def trio: Vec Nat 3 := VCons 1 (VCons 2 (VCons 3 VNil))

-- `head` only accepts a vector that is not empty: no default, no error.
def first (v: Vec Nat 3): Nat := v.head

-- Zipping needs equal lengths, and the type says so.
def sums (a b: Vec Nat 3): Vec Nat 3 := a.zipWith b (x y => x + y)

test "head" := first trio == 1
test "sum" := (sums trio trio).sum == 12
