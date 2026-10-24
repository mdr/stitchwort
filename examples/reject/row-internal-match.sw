-- expect-error: E-INTERNAL
-- Matching on a row's constructors is refused too (D1122).
import Std.Effect (Row)
import Std.Effect.Row (Empty, Ops)

def isPure: Row -> Bool
  | Empty => True
  | Ops op res => False
