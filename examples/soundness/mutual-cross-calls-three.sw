-- expect-error: E-TERMINATION
-- CVE-2026-72703 with three members: `f` makes its list smaller, but `g`
-- and `h` each put a cell back, so going round `f → g → h → f` it grows.
-- Neighbour: `total`/`inner` in accept/mutual.sw.
def f: List Nat → Void
  | Nil => g Nil
  | Cons x xs => g xs

def g (xs: List Nat): Void := h (Cons 0 xs)

def h (xs: List Nat): Void := f (Cons 1 xs)
