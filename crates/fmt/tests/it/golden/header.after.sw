-- R1: header continuation lines at +4, wherever they were.
theorem long (a: Nat) (b: Nat)
    (c: Nat): a + b + c = c + b + a :=
  omega

def deep (x: Nat)
    (y: Nat): Nat := x + y

-- A `decreasing` line is a header line; a bare `:=` at column 0 stays (R21).
def count (n: Nat): Nat
    decreasing n
:=
  if h: n == 0 then 0 else count (n - 1)
