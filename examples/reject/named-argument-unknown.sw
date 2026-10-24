-- expect-error: E-UNKNOWN-NAME
-- A name the function's parameters don't have: the error lists them, with
-- their kinds (docs/proposals/named-arguments.md §6.3).

def between [step: Nat] (low: Nat) (high: Nat): Nat := high - low + step

def window: Nat := between (low := 1) (middle := 5)
