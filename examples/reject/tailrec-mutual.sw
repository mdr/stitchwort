-- expect-error: E-TAILREC
-- Calls between mutually recursive definitions aren't covered yet.
import Std (Nat)

@[tailrec]
def isEven: Nat → Bool
  | 0 => True
  | Succ n => isOdd n

def isOdd: Nat → Bool
  | 0 => False
  | Succ n => isEven n
