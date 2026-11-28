-- expect-error: E-TERMINATION
-- A stream that refers to itself has no argument to get smaller, so it is
-- refused; the error points to `Stream.repeat`, `iterate` and `unfold`.
import Std (Stream)

def ones: Stream Nat := Stream.cons 1 ones
