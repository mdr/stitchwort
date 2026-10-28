-- A call in an open partial row whose tail is solved while it's checked:
-- `inner`'s `e` is solved as `outer`'s, and the results of the row it
-- expects, written with that unknown, are still the row's own once it's
-- solved. So the call is a computation in the row, not a value of some
-- other `Comp` (SW-851; the shape of accept/adder.sw's `step`).
ability Log where
  log: (n: Nat) → {Log} ()

def inner (n: Nat) (more: Nat → {Log, Partial | e} Nat): {Log, Partial | e} Nat :=
  log n
  more n

def outer (b: Bool) (more: Nat → {Log, Partial | e} Nat): {Log, Partial | e} Nat :=
  if b then 0 else inner 1 more
