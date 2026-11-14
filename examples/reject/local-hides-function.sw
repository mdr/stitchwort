-- expect-error: E-TYPE-MISMATCH
-- The parameter `size` hides the function `size`, and the code meant the
-- function: `size` alone has the parameter's type, so say which function is
-- hidden.
def size (x: Nat): Nat := x

def f (size: Nat): Nat -> Nat := size
