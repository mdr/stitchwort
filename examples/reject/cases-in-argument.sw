-- expect-error: E-PARSE
-- `cases then t` takes the rest of the expression as `t`, so as an argument it
-- needs brackets: `andRight a b (cases then both)`.
import Std (Bool, Nat)

theorem andRight (a: Bool) (b: Bool) (both: (a ∧ b) = True): b = True := cases

theorem orOfAnd (a: Bool) (b: Bool) (both: (a ∧ b) = True): (b ∨ a) = True :=
  let right := andRight a b cases then both
  cases
