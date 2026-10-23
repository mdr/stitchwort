-- expect-error: E-NONEXHAUSTIVE
-- Number patterns on a `Fin n` are `FZero` and `FSucc` (D1073), so a match
-- that leaves a number out is incomplete. The missing case is reported as
-- the number, 1, not as the `FZero` one level down (D1079).
import Std (Fin)

def name: Fin 3 -> Text
  | 0 => "zero"
  | 2 => "two"
