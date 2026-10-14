-- expect-error: E-NOT-EMPTY
-- `()` claims the argument can't exist, but there are natural numbers.
wrong : Nat -> Nat
wrong ()
