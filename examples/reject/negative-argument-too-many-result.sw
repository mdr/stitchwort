-- expect-error: E-TYPE-MISMATCH
-- `k x -1` passes `-1` as a second argument, so the call is an `Int` where a
-- function is expected (a mismatch at the result, not `E-NOT-A-FUNCTION`); the
-- note says `-1` is an argument, not a subtraction.
def k (a: Int) (b: Int): Int := a

def h (x: Int): Int -> Int -> Int := k x -1
