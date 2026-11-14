-- expect-error: E-PARSE
-- The `∀` before a header's parameters (D3472) is for theorems; a `def` lists
-- its parameters straight after its name.
def double ∀ (n: Nat): Nat := n + n
