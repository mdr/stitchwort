-- expect-error: E-PARTIAL-ESCAPE
-- A recursive call returned as part of the result: nothing outside
-- `retry`'s definition could answer its request. Returning a closure over a
-- partial function that's already defined is fine (`retryWith` in
-- accept/partial.sw).
retry : Nat -> {Partial} (Nat -> {Partial} Nat)
retry n = \x -> retry (n - 1) x
