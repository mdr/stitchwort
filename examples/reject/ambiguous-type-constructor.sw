-- expect-error: E-AMBIGUOUS
-- A type and its only constructor have the same name. The constructor can be
-- written `YUp.YUp`, but the type has no qualified form: rename the
-- constructor.
type YUp: Type =
  | YUp

def yUpCount (y: YUp): Nat := 0

def make: YUp := YUp
