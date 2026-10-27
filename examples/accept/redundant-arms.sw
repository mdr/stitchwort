-- expect-warning: W-REDUNDANT
-- An arm that earlier arms always take first is never chosen, and warns
-- (W-REDUNDANT), as does an alternative of an or-pattern that earlier arms
-- or alternatives cover. The warnings don't stop the program from being
-- accepted.
import Std (Bool)

type Colour = | Red | Green | Blue

-- The same literal twice: the second `'k'` arm is never chosen.
def key: Char → Nat
  | 'k' => 1
  | 'w' => 2
  | 'k' => 3
  | _ => 0

-- A constructor arm after a catch-all.
def isRed: Colour → Bool
  | Red => True
  | _ => False
  | Blue => False

-- An alternative an earlier arm covers, and one an earlier alternative does.
def step: Char → Nat
  | 'h' => 0
  | 'h' | 'j' => 1
  | 'l' | 'l' => 2
  | _ => 3

-- In a `match`, several earlier arms together cover the last one.
def both (first: Bool) (second: Bool): Nat :=
  match first, second with
    | True, _ => 1
    | _, True => 2
    | False, False => 3
    | False, _ => 4

test "key" := ['k', 'w', 'x'].map key == [1, 2, 0]
test "isRed" := [Red, Green, Blue].map isRed == [True, False, False]
test "step" := ['h', 'j', 'l', 'x'].map step == [0, 1, 2, 3]
test "both" := [both True False, both False True, both False False] == [1, 2, 3]
