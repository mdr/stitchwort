-- expect-error: E-DUPLICATE
-- A row has each ability at most once.
ability State (s : Type) where
  get : () -> {State s} s

def both () : {State Nat, State Bool} Nat := get ()
