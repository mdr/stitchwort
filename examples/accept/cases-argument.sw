-- `cases` is a whole term, so it can be an argument, as `omega` can: at the
-- end of a line, before the next line of the block, too.
import Std (Bool, Nat)

theorem andRight (a: Bool) (b: Bool) (both: (a ∧ b) = True): b = True := cases

theorem orOfAnd (a: Bool) (b: Bool) (both: (a ∧ b) = True): (b ∨ a) = True :=
  let right := andRight a b cases
  cases

theorem orOfAndMiddle (a: Bool) (b: Bool) (both: (a ∧ b) = True): (b ∨ a) = True :=
  let right := andRight a b cases |> (proof => proof)
  cases
