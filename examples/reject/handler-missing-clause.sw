-- expect-error: E-HANDLER
-- A handler that removes `State` needs a clause for each operation.
ability State where
  get : () -> {State} Nat
  put : Nat -> {State} ()

def onlyGet (prog : () -> {State | e} a) : {e} a :=
  handle prog () with
    | return x   => x
    | get u, k => k 0
