-- expect-error: E-TERMINATION
-- A callback kept after its creator returns, rebuilding the parameter
-- (docs/proposals/mutual-recursion.md §6.3 test 2): `make (Cons n rest)`
-- returns a callback that calls `weigh (Cons n rest) x`, which calls `make`
-- on the same list again. Nothing gets smaller. (`weigh [1] 0` loops.)
-- Neighbour: accept/mutual-callback.sw, which passes `rest`.
type Callback = { call: Nat -> Nat }

def make: List Nat -> Callback
  | Nil => { call = x => x }
  | Cons n rest => { call = x => weigh (Cons n rest) x }

def weigh (xs: List Nat) (x: Nat): Nat :=
  let callback: Callback := make xs
  callback.call x
