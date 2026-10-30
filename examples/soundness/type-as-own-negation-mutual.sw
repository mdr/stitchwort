-- expect-error: E-TERMINATION
-- `T ≡ T → False` through a second member, each call on a larger number.
-- Neighbour: `isEven`/`isOdd` in accept/mutual.sw.
def T (n: Nat): Prop := U (Succ n)

def U (n: Nat): Prop := T (Succ n) → Void
