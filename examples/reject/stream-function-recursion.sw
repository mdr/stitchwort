-- expect-error: E-TERMINATION
-- The same note for a function that returns a stream and calls itself for
-- the rest of it: nothing gets smaller.
import Std (Stream)

def from (n: Nat): Stream Nat := Stream.cons n (from (n + 1))
