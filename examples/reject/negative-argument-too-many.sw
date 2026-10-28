-- expect-error: E-NOT-A-FUNCTION
-- `g x -1` passes `-1` to `g x`, which is already a number.
def g (n: Int): Int := n

def h (x: Int): Int := g x -1
