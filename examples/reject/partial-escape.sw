-- expect-error: E-PARTIAL-ESCAPE
-- A recursive call returned as part of the result: nothing outside
-- `retry`'s definition could answer its request. Returning a closure over a
-- partial function that's already defined is fine (`retryWith` in
-- accept/partial.sw).
def retry (n: Nat): {Partial} (Nat -> {Partial} Nat) := \x => retry (n - 1) x
