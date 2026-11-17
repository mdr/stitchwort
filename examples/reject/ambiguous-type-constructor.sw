-- expect-error: E-AMBIGUOUS
-- A type and its only constructor have the same name. Where a type is
-- written (`y: YUp`) the name is the type; where a value is wanted it is
-- ambiguous, and the constructor is written `YUp.YUp`.
type YUp: Type =
  | YUp

def yUpCount (y: YUp): Nat := 0

def make: YUp := YUp
