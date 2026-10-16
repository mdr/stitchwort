-- expect-error: E-PARTIAL
-- A handler folds over every way a computation can go, so the computation
-- it handles must finish: it can't be partial. (Its clauses may run
-- partial code: `countLogged` in accept/partial.sw.)
ability Log where
  say : Nat -> {Log} ()

spin : Nat -> {Partial} Nat
spin n = spin (n + 1)

loud : () -> {Log, Partial} Nat
loud u =
  say 1
  spin 0

quiet : () -> {Partial} Nat
quiet u =
  handle loud () with
    | return x   -> x
    | say n => k -> k ()
