-- expect-error: E-ATTRIBUTE
-- A definition that isn't exported never crosses to JavaScript.
@[js.name "double"]
def twice (n: Nat): Nat := n + n
