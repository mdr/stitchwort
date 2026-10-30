-- expect-error: E-ABILITY
-- An argument passed to a parameter of computation type is a computation
-- in the parameter's abilities, not the caller's. `pass` takes a `Comp` in
-- the empty row (its results `r` are unknown at the call, so they become
-- the row's, SW-851), and `log 3` performs `Log`. `caller` may perform
-- `Log`, so the error says what the parameter takes, not that `Log` isn't
-- in the enclosing function's abilities, which is false (SW-871).
import Std.Effect (Comp, NoOp)

ability Log where
  log: (n: Nat) → {Log} ()

def pass (c: Comp NoOp r Nat): Nat := 0

def caller (): {Log} Nat := pass (log 3)

-- The same when the call itself performs `Log`.
def passLog (c: Comp NoOp r Nat): {Log} Nat :=
  log 1
  1

def callerLog (): {Log} Nat := passLog (log 3)
