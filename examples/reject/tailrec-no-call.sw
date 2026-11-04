-- expect-error: E-TAILREC
-- It never calls itself: the recursion moved into a helper.
import Std (Nat)

@[tailrec]
def f (n: Nat): Nat := n + 1
