-- A callback kept after its creator returns, for a group, extracted to
-- JavaScript (docs/proposals/mutual-recursion.md §6.3 test 2): `make`
-- returns a record holding a closure over `n` and `rest` that calls
-- `weigh`, another member, after `make` has returned.
--
-- run: weigh [1, 2, 3] 10
-- run: twice [1, 2] 0
-- run: twice [] 7

type Callback = { call: Nat -> Nat }

def make: List Nat -> Callback
  | Nil => { call = x => x }
  | Cons n rest => { call = x => weigh rest x + n }

export def weigh (xs: List Nat) (x: Nat): Nat :=
  let callback: Callback := make xs
  callback.call x

export def twice (xs: List Nat) (x: Nat): Nat :=
  let callback: Callback := make xs
  callback.call (callback.call x)
