-- Unary minus is tight (`-x`); binary minus has a space on each side.
def neg (x: Int): Int := -x
def sub (x: Int) (y: Int): Int := x - y
def both (x: Int): Int := -x - -x
def twice (x: Int): Int := - -x
def nots (b: Bool): Bool := !b
def cmp (x: Int): Bool := x == -1 && !(x < -2)
def list: List Int := [-1, -2, 3]
theorem back (h: a = b): b = a := rewrite <- h in rfl
def lines (x: Int): Int :=
  x
    - 1
