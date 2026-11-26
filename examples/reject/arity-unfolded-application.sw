-- expect-error: E-NOT-A-FUNCTION
-- A definition whose type unfolds to a function type: the error should say
-- which definition it unfolded.
def Pred: Type := Nat → Bool

def isZero: Pred := n => n == 0

def tooMany: Bool := isZero 0 1
