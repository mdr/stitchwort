-- expect-error: E-INTERNAL
-- Matching on a row's constructors is refused too (D1122).
import Std.Effect (Effects)
import Std.Effect.Effects (Empty, Ops)

def isPure: Effects -> Bool
  | Empty => True
  | Ops op res => False
