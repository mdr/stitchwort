-- expect-error: E-TERMINATION
-- The same in the tail form: the `match` is part of the equation's case tree.
loop : Nat -> Nat
loop n = match Succ n with
  | Zero   -> 0
  | Succ k -> loop k
