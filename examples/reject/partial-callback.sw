-- expect-error: E-PARTIAL-CALLBACK
-- Inside its definition, `loop` as a value makes requests that only
-- `loop`'s own definition can answer, so it can't be passed to a helper
-- whose callback has a fixed row. The helper must be polymorphic in the
-- rest of the row, `(Nat -> {Partial | e} Nat) -> Nat -> {Partial | e} Nat`,
-- as `useP` in accept/partial.sw is (docs/proposals/partial.md §7.3.4).
def useP (k : Nat -> {Partial} Nat) (n : Nat) : {Partial} Nat := k n

def loop (n : Nat) : {Partial} Nat := useP loop n
