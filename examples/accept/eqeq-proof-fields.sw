-- Derived `==` (`DecEq`) for types with value parameters and with proof
-- fields that are equations (docs/proposals/interfaces.md §5.11, D179). The
-- proofs aren't compared: any two proofs of an equation in a type with
-- `DecEq` are equal (`DecEq.uniqueEq`, Hedberg's theorem), and the derived
-- proof that equal data gives equal values says so.

import Std (DecEq, List, Nat)

-- A value parameter, and a proof field `position <= highest`, which is the
-- equation `Nat.leq position highest = True` in `Bool`.
type Dial (highest: Nat) = { position: Nat, inRange: position ≤ highest }

def dial3: Dial 10 := { position = 3, inRange = byComputing }
def other3: Dial 10 := { position = 3, inRange = byComputing }
def dial4: Dial 10 := { position = 4, inRange = byComputing }

test "dials" := dial3 == other3
test "different dials" := dial3 ≠ dial4
test "if h" := if h: dial3 = other3 then True else False

-- A data type whose constructor has a proof field between data fields.
type Small = | MkSmall (n: Nat) (small: Nat.leq n 10 = True) (label: Text) | Big

test "small" := MkSmall 3 byComputing "x" == MkSmall 3 byComputing "x"
test "small, label differs" := MkSmall 3 byComputing "x" ≠ MkSmall 3 byComputing "y"
test "small and big" := MkSmall 3 byComputing "x" ≠ Big

-- A record with a parameter and an equation in `Nat`.
type Short (a: Type) = {
  items: List a,
  size: Nat,
  ok: List.length items = size
}

def short: Short Text := { items = ["a"], size = 1, ok = byComputing }

test "short" := short == { items = ["a"], size = 1, ok = byComputing }
test "short, items differ" := short ≠ { items = ["b"], size = 1, ok = byComputing }

-- The theorem itself.
theorem bothProofs ∀ (p q: Nat.leq 3 10 = True): p = q := DecEq.uniqueEq p q
