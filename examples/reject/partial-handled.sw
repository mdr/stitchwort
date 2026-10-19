-- expect-error: E-PARTIAL
-- A handler folds over every way a computation can go, so the computation
-- it handles must finish: it can't be partial. (Its clauses may run
-- partial code: `countLogged` in accept/partial.sw.)
ability Log where
  say: Nat -> {Log} ()

def spin (n: Nat): {Partial} Nat := spin (n + 1)

def loud (): {Log, Partial} Nat :=
  say 1
  spin 0

def quiet (): {Partial} Nat :=
  handle loud () with
    | return x   => x
    | say n, k => k ()
