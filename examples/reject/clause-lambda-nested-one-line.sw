-- expect-error: E-NONEXHAUSTIVE
-- On one line, an inner `match` takes every arm after it, so `| Square => 3`
-- is the inner `match r with`'s, and the outer one has no arm for `Square`.
-- Bracket the inner `match`, or put the arms on lines.
import Std (Nat)

type Shape =
  | Circle (radius: Nat)
  | Square

def area: Shape → Nat := match | Circle r => match r with | 0 => 1 | _ => 2 | Square => 3
