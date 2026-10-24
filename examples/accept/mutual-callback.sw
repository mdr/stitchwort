-- A callback kept after its creator returns, for a group
-- (docs/proposals/mutual-recursion.md §6.3 test 2, §6.4 step 4): `make`
-- returns a record holding `x => weigh rest x`, and `weigh`, another member
-- of the group, calls it only after `make` has returned. The call
-- `weigh rest x` has `rest` smaller than `make`'s parameter, so it is
-- accepted, however late or often the callback is called.
-- Rejected neighbours: soundness/mutual-callback-rebuild.sw,
-- soundness/mutual-callback-lambda.sw.
import Std (IO, Nat)

type Callback = { call: Nat -> Nat }

def make: List Nat -> Callback
  | Nil => { call = x => x }
  | Cons n rest => { call = x => weigh rest x + n }

def weigh (xs: List Nat) (x: Nat): Nat :=
  let callback: Callback := make xs
  callback.call x

-- A final definition, outside the group, which keeps the callback and calls
-- it twice.
def twice (xs: List Nat) (x: Nat): Nat :=
  let callback: Callback := make xs
  callback.call (callback.call x)

-- Run by the fast runtime, the reference evaluator and `run --js`, which
-- must print the same: 16 6 7.
def main(): {IO} () :=
  IO.print (Nat.toText (weigh [1, 2, 3] 10) ++ " " ++ Nat.toText (twice [1, 2] 0) ++ " " ++ Nat.toText (twice [] 7))

test "weigh adds the list" := weigh [1, 2, 3] 10 == 16
test "twice" := twice [1, 2] 0 == 6
test "empty list" := twice [] 7 == 7

theorem weighExample: weigh [1, 2, 3] 10 = 16 := rfl
theorem twiceExample: twice [1, 2] 0 = 6 := rfl
