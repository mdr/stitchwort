-- expect-error: E-TERMINATION
-- `Succ n` rebuilds the argument itself, not something smaller, so this
-- loops. (Compare `fib` in accept/nested-patterns.sw, where `Succ n`
-- rebuilds a value *inside* the argument.)
def loop : Nat -> Nat
  | 0      => 0
  | Succ n => loop (Succ n)
