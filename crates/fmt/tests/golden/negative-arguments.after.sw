-- D1472: an argument minus keeps its form: `f -2` and `f (-2)` both stay.
-- The gap before it is kept, the one after it is none.
def f (n: Int): Int := n

def a: Int := f -2

def b (x: Int): Int := f -x

def c: Int := f (-2)

def d (n: Int): Int := n - 1

def e (n: Int): Int := n - 1

def g (n: Int): Int :=
  f
    -n

def h (x: Int) (y: Int): Int :=
  x
    - y

def i (x: Int) (y: Int): Int :=
  let z := x + y
  - z

def j: Int := - 1.abs

def k: Int := -1.abs

def l (xs: List Int): List Int := xs.map (x => f -x)
