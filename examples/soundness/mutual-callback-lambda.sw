-- expect-error: E-TERMINATION
-- A callback kept after its creator returns, whose argument is the
-- lambda's own variable (docs/proposals/mutual-recursion.md §6.4 step 4):
-- the callback is `ys => weigh ys`, and `ys` is lambda-bound, so it is not
-- known to be smaller than anything. The callback is called later on
-- whatever the caller likes, including the list `make` was given.
-- (`weigh []` loops.)
-- Neighbour: accept/mutual-callback.sw, whose callback calls `weigh` on
-- `rest`, which was matched out of `make`'s parameter.
type Callback = { call: List Nat → Nat }

def make: List Nat → Callback
  | Nil => { call = ys => weigh ys }
  | Cons _ rest => { call = ys => weigh rest }

def weigh (xs: List Nat): Nat :=
  let callback: Callback := make xs
  callback.call xs
