-- A theorem's statement may start with a record literal or update, as a body
-- can (SW-1015). After a declaration's `:`, braces are an ability row only
-- when a type follows them.

import Std (Eq, Nat)

type Point = { id: Nat, x: Nat }

def moveTo (p: Point) (n: Nat): Point := { p | x = n }

theorem updateField (p: Point): { p | x = 3 }.x = 3 := rfl

theorem literalField: { id = 2, x = 1 }.x = 1 := rfl

theorem literalEq: { id = 2, x = 1 } = moveTo { id = 2, x = 0 } 1 := rfl

-- An update with a punned field, followed by `.x`.
theorem punned (p: Point) (x: Nat): { p | x }.x = x := rfl

-- After an arrow, too.
theorem afterArrow (p: Point): { p | id = 7 }.id = 7 := rfl

-- Rows are as before.
def answer: {} Nat := 42
