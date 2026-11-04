-- expect-error: E-PARSE
-- `..` needs a list after it.
def f: List Nat := [1, ..]
