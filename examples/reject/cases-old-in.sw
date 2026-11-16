-- expect-error: E-PARSE
-- `cases then t` (D3648); the old spelling `cases in t` is an error naming
-- `then`.
import Std (Bool)

theorem andLeft (a b: Bool) (h: (a ∧ b) = True): a = True :=
  cases in h
