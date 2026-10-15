-- expect-error: E-HANDLER
-- A handler that removes `State` needs a clause for each operation.
ability State where
  get : () -> {State} Nat
  put : Nat -> {State} ()

onlyGet : (() -> {State | e} a) -> {e} a
onlyGet prog =
  handle prog () with
    | return x   -> x
    | get u => k -> k 0
