-- expect-error: E-TERMINATION
-- A constructor rebuilt from a nested pattern's parts is that part only if
-- every field is the matched one. `Nil` fits a list of any type, so it
-- doesn't pin `a`: `Mk [a := Bool] Nil rest` isn't the inner `Mk` (paired
-- with `nonEmptyRun` in accept/structural-rebuilt-pattern.sw).
type Box: Type 1 =
  | Stop
  | Mk [a: Type] (xs: List a) (rest: Box)

def spin: Box → Nat
  | Mk Nil (Mk Nil rest) => spin (Mk [a := Bool] Nil rest)
  | other => 0
