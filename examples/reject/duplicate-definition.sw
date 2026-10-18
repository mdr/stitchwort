-- expect-error: E-DUPLICATE
-- `length` is defined twice in this file.
def length : Nat := 0

def length : Nat := 1
