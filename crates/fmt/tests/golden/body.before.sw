-- R2: a body on the next line after `:=` or `=>` at +2, block lines at the
-- block's column.
def f (x: Nat): Nat :=
      let y := x + 1
      let z :=
              y * 2
      z

def g: Nat -> Nat := x =>
    x + 1

def h (x: Nat): Nat :=
    match x with
          | Zero => 0
          | Succ k => k

ability Log where
    say: Nat -> {Log} ()

test "a test" :=
    f 1 == 4
