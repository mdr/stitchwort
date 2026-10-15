-- expect-error: E-TERMINATION
-- `Succ n` rebuilds the argument itself, not something smaller, so this
-- loops. (Compare `fib` in accept/nested-patterns.sw, where `Succ n`
-- rebuilds a value *inside* the argument.)
loop : Nat -> Nat
loop 0        = 0
loop (Succ n) = loop (Succ n)
