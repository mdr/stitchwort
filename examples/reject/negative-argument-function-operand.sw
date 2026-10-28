-- expect-error: E-TYPE-MISMATCH
-- `f -g x` is `f (-g) x`: the `-` negates `g` alone, and `g` is a function.
def f (a: Int) (b: Int): Int := a + b

def g (n: Int): Int := n

def h (x: Int): Int := f -g x
