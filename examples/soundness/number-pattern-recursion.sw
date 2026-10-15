-- expect-error: E-TERMINATION
-- Matching a number doesn't make anything smaller: `n` here is the whole
-- argument. (accept/number-patterns.sw has `countDown`, whose recursion goes
-- through a `Succ` pattern.)
loop : Nat -> Nat
loop 404 = 0
loop n   = loop n
